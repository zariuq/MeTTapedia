import Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics

/-!
# Prenex normalization for canonical TPTP FOF NNF

Skolemization has a simple, reusable model-extension theorem on prenex input.
This module supplies the preceding equivalence-preserving stage.  Quantifiers
are pulled across conjunction and disjunction with explicit de Bruijn shifts;
no source spelling participates in capture avoidance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics

open LO FirstOrder
open scoped LO.FirstOrder
open Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics

abbrev Formula (depth : Nat) :=
  LO.FirstOrder.Semiformula language Empty depth

/-- Matrix formulas contain no quantifier. -/
def QuantifierFree {depth : Nat} : Formula depth -> Prop
  | .verum | .falsum | .rel _ _ | .nrel _ _ => True
  | .and left right | .or left right =>
      QuantifierFree left /\ QuantifierFree right
  | .all _ | .ex _ => False

/-- A prenex NNF has one quantifier prefix followed by a quantifier-free
matrix. -/
inductive Prenex : {depth : Nat} -> Formula depth -> Prop
  | matrix {depth : Nat} {formula : Formula depth} :
      QuantifierFree formula -> Prenex formula
  | all {depth : Nat} {body : Formula (depth + 1)} :
      Prenex body -> Prenex (.all body)
  | ex {depth : Nat} {body : Formula (depth + 1)} :
      Prenex body -> Prenex (.ex body)

/-- A computational prenex object whose shape itself enforces the prefix
boundary. -/
inductive PrenexForm : Nat -> Type
  | matrix {depth : Nat} (formula : Formula depth)
      (quantifierFree : QuantifierFree formula) : PrenexForm depth
  | all {depth : Nat} (body : PrenexForm (depth + 1)) : PrenexForm depth
  | ex {depth : Nat} (body : PrenexForm (depth + 1)) : PrenexForm depth

def PrenexForm.toFormula {depth : Nat} : PrenexForm depth -> Formula depth
  | .matrix formula _ => formula
  | .all body => .all body.toFormula
  | .ex body => .ex body.toFormula

def PrenexForm.quantifierCount {depth : Nat} : PrenexForm depth -> Nat
  | .matrix _ _ => 0
  | .all body | .ex body => body.quantifierCount + 1

theorem PrenexForm.toFormula_prenex {depth : Nat}
    (form : PrenexForm depth) : Prenex form.toFormula := by
  induction form with
  | matrix formula quantifierFree => exact .matrix quantifierFree
  | all body inductionHypothesis => exact .all inductionHypothesis
  | ex body inductionHypothesis => exact .ex inductionHypothesis

theorem quantifierFree_rew {sourceDepth targetDepth : Nat}
    (rewriting : LO.FirstOrder.Rew language Empty sourceDepth Empty targetDepth)
    {formula : Formula sourceDepth} (quantifierFree : QuantifierFree formula) :
    QuantifierFree (rewriting ▹ formula) := by
  induction formula generalizing targetDepth with
  | verum => trivial
  | falsum => trivial
  | rel => trivial
  | nrel => trivial
  | and left right leftHypothesis rightHypothesis =>
      exact ⟨leftHypothesis rewriting quantifierFree.1,
        rightHypothesis rewriting quantifierFree.2⟩
  | or left right leftHypothesis rightHypothesis =>
      exact ⟨leftHypothesis rewriting quantifierFree.1,
        rightHypothesis rewriting quantifierFree.2⟩
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

/-- Apply a binder rewriting to a complete prenex object. -/
def PrenexForm.rew {sourceDepth targetDepth : Nat}
    (rewriting : LO.FirstOrder.Rew language Empty sourceDepth Empty targetDepth) :
    PrenexForm sourceDepth -> PrenexForm targetDepth
  | .matrix formula quantifierFree =>
      .matrix (rewriting ▹ formula)
        (quantifierFree_rew rewriting quantifierFree)
  | .all body => .all (body.rew rewriting.q)
  | .ex body => .ex (body.rew rewriting.q)

theorem PrenexForm.rew_quantifierCount_exact
    {sourceDepth targetDepth : Nat}
    (rewriting : LO.FirstOrder.Rew language Empty sourceDepth Empty targetDepth)
    (form : PrenexForm sourceDepth) :
    (form.rew rewriting).quantifierCount = form.quantifierCount := by
  induction form generalizing targetDepth with
  | matrix => rfl
  | all body inductionHypothesis =>
      simp [PrenexForm.rew, PrenexForm.quantifierCount, inductionHypothesis]
  | ex body inductionHypothesis =>
      simp [PrenexForm.rew, PrenexForm.quantifierCount, inductionHypothesis]

theorem PrenexForm.rew_toFormula_exact
    {sourceDepth targetDepth : Nat}
    (rewriting : LO.FirstOrder.Rew language Empty sourceDepth Empty targetDepth)
    (form : PrenexForm sourceDepth) :
    (form.rew rewriting).toFormula = rewriting ▹ form.toFormula := by
  induction form generalizing targetDepth with
  | matrix => rfl
  | all body inductionHypothesis =>
      rw [PrenexForm.rew, PrenexForm.toFormula,
        inductionHypothesis]
      exact (Rewriting.app_all rewriting body.toFormula).symm
  | ex body inductionHypothesis =>
      rw [PrenexForm.rew, PrenexForm.toFormula,
        inductionHypothesis]
      exact (Rewriting.app_ex rewriting body.toFormula).symm

inductive Connective
  | and
  | or
  deriving DecidableEq, Repr

def Connective.apply {depth : Nat} :
    Connective -> Formula depth -> Formula depth -> Formula depth
  | .and => .and
  | .or => .or

def Connective.holds : Connective -> Prop -> Prop -> Prop
  | .and => And
  | .or => Or

private theorem Connective.holds_congr (connective : Connective)
    {first first' second second' : Prop}
    (firstExact : first <-> first') (secondExact : second <-> second') :
    connective.holds first second <->
      connective.holds first' second' := by
  cases connective <;> simp [Connective.holds, firstExact, secondExact]

private theorem forall_connective_left {Domain : Type} [Nonempty Domain]
    (connective : Connective) (predicate : Domain -> Prop) (constant : Prop) :
    (forall value, connective.holds (predicate value) constant) <->
      connective.holds (forall value, predicate value) constant := by
  classical
  cases connective with
  | and =>
      constructor
      · intro holds
        exact ⟨fun value => (holds value).1,
          (holds (Classical.choice inferInstance)).2⟩
      · rintro ⟨allPredicate, holdsConstant⟩ value
        exact ⟨allPredicate value, holdsConstant⟩
  | or =>
      by_cases holdsConstant : constant <;>
        simp [Connective.holds, holdsConstant]

private theorem forall_connective_right {Domain : Type} [Nonempty Domain]
    (connective : Connective) (constant : Prop) (predicate : Domain -> Prop) :
    (forall value, connective.holds constant (predicate value)) <->
      connective.holds constant (forall value, predicate value) := by
  classical
  cases connective with
  | and =>
      constructor
      · intro holds
        exact ⟨(holds (Classical.choice inferInstance)).1,
          fun value => (holds value).2⟩
      · rintro ⟨holdsConstant, allPredicate⟩ value
        exact ⟨holdsConstant, allPredicate value⟩
  | or =>
      by_cases holdsConstant : constant <;>
        simp [Connective.holds, holdsConstant]

private theorem exists_connective_left {Domain : Type} [Nonempty Domain]
    (connective : Connective) (predicate : Domain -> Prop) (constant : Prop) :
    (exists value, connective.holds (predicate value) constant) <->
      connective.holds (exists value, predicate value) constant := by
  classical
  cases connective with
  | and =>
      constructor
      · rintro ⟨value, holdsPredicate, holdsConstant⟩
        exact ⟨⟨value, holdsPredicate⟩, holdsConstant⟩
      · rintro ⟨⟨value, holdsPredicate⟩, holdsConstant⟩
        exact ⟨value, holdsPredicate, holdsConstant⟩
  | or =>
      by_cases holdsConstant : constant <;>
        simp [Connective.holds, holdsConstant]

private theorem exists_connective_right {Domain : Type} [Nonempty Domain]
    (connective : Connective) (constant : Prop) (predicate : Domain -> Prop) :
    (exists value, connective.holds constant (predicate value)) <->
      connective.holds constant (exists value, predicate value) := by
  classical
  cases connective with
  | and =>
      constructor
      · rintro ⟨value, holdsConstant, holdsPredicate⟩
        exact ⟨holdsConstant, ⟨value, holdsPredicate⟩⟩
      · rintro ⟨holdsConstant, ⟨value, holdsPredicate⟩⟩
        exact ⟨value, holdsConstant, holdsPredicate⟩
  | or =>
      by_cases holdsConstant : constant <;>
        simp [Connective.holds, holdsConstant]

/-- Pull both prenex prefixes across one Boolean connective. -/
def combine {depth : Nat} (connective : Connective)
    (left right : PrenexForm depth) : PrenexForm depth :=
  match left, right with
  | .all leftBody, right =>
      .all (combine connective leftBody
        (right.rew LO.FirstOrder.Rew.bShift))
  | .ex leftBody, right =>
      .ex (combine connective leftBody
        (right.rew LO.FirstOrder.Rew.bShift))
  | left@(.matrix _ _), .all rightBody =>
      .all (combine connective
        (left.rew LO.FirstOrder.Rew.bShift) rightBody)
  | left@(.matrix _ _), .ex rightBody =>
      .ex (combine connective
        (left.rew LO.FirstOrder.Rew.bShift) rightBody)
  | .matrix leftFormula leftQf, .matrix rightFormula rightQf =>
      .matrix (connective.apply leftFormula rightFormula) <| by
        cases connective <;> exact ⟨leftQf, rightQf⟩
termination_by left.quantifierCount + right.quantifierCount
decreasing_by
  all_goals
    simp [PrenexForm.quantifierCount,
      PrenexForm.rew_quantifierCount_exact, *]

abbrev Eval {Domain : Type}
    (interpretation : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (environment : Fin depth -> Domain)
    (formula : Formula depth) : Prop :=
  LO.FirstOrder.Semiformula.EvalAux interpretation Empty.elim environment formula

theorem PrenexForm.eval_rew_bShift_exact {Domain : Type}
    (interpretation : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (environment : Fin depth -> Domain) (value : Domain)
    (form : PrenexForm depth) :
    Eval interpretation (value :> environment)
        (form.rew LO.FirstOrder.Rew.bShift).toFormula <->
      Eval interpretation environment form.toFormula := by
  rw [form.rew_toFormula_exact]
  exact LO.FirstOrder.Semiformula.eval_bShift
    (s := interpretation) (e := environment) (x := value) (ε := Empty.elim)
    form.toFormula

theorem termPrincipalSymbols_map_exact {sourceDepth targetDepth : Nat}
    (mapping : Fin sourceDepth -> Fin targetDepth)
    (term : LO.FirstOrder.Semiterm language Empty sourceDepth) :
    termPrincipalSymbols (LO.FirstOrder.Rew.map mapping id term) =
      termPrincipalSymbols term := by
  induction term with
  | bvar => rfl
  | fvar impossible => exact nomatch impossible
  | func symbol arguments inductionHypothesis =>
      rw [LO.FirstOrder.Rew.func]
      simp only [termPrincipalSymbols]
      have argumentsExact :
          Finset.univ.biUnion (fun index =>
              termPrincipalSymbols
                (LO.FirstOrder.Rew.map mapping id (arguments index))) =
            Finset.univ.biUnion (fun index =>
              termPrincipalSymbols (arguments index)) := by
        apply Finset.biUnion_congr rfl
        intro index _
        exact inductionHypothesis index
      rw [argumentsExact]

theorem nnfPrincipalSymbols_map_exact {sourceDepth targetDepth : Nat}
    (mapping : Fin sourceDepth -> Fin targetDepth)
    (formula : Formula sourceDepth) :
    nnfPrincipalSymbols (LO.FirstOrder.Rew.map mapping id ▹ formula) =
      nnfPrincipalSymbols formula := by
  induction formula generalizing targetDepth with
  | verum => rfl
  | falsum => rfl
  | rel relation arguments =>
      rw [LO.FirstOrder.Semiformula.rew_rel]
      simp only [nnfPrincipalSymbols]
      have argumentsExact :
          Finset.univ.biUnion (fun index =>
              termPrincipalSymbols
                (LO.FirstOrder.Rew.map mapping id (arguments index))) =
            Finset.univ.biUnion (fun index =>
              termPrincipalSymbols (arguments index)) := by
        apply Finset.biUnion_congr rfl
        intro index _
        exact termPrincipalSymbols_map_exact mapping (arguments index)
      rw [argumentsExact]
  | nrel relation arguments =>
      rw [LO.FirstOrder.Semiformula.rew_nrel]
      simp only [nnfPrincipalSymbols]
      have argumentsExact :
          Finset.univ.biUnion (fun index =>
              termPrincipalSymbols
                (LO.FirstOrder.Rew.map mapping id (arguments index))) =
            Finset.univ.biUnion (fun index =>
              termPrincipalSymbols (arguments index)) := by
        apply Finset.biUnion_congr rfl
        intro index _
        exact termPrincipalSymbols_map_exact mapping (arguments index)
      rw [argumentsExact]
  | and left right leftHypothesis rightHypothesis =>
      change
        nnfPrincipalSymbols (LO.FirstOrder.Rew.map mapping id ▹ left) ∪
            nnfPrincipalSymbols (LO.FirstOrder.Rew.map mapping id ▹ right) =
          nnfPrincipalSymbols left ∪ nnfPrincipalSymbols right
      rw [leftHypothesis mapping, rightHypothesis mapping]
  | or left right leftHypothesis rightHypothesis =>
      change
        nnfPrincipalSymbols (LO.FirstOrder.Rew.map mapping id ▹ left) ∪
            nnfPrincipalSymbols (LO.FirstOrder.Rew.map mapping id ▹ right) =
          nnfPrincipalSymbols left ∪ nnfPrincipalSymbols right
      rw [leftHypothesis mapping, rightHypothesis mapping]
  | all body inductionHypothesis =>
      change
        nnfPrincipalSymbols
            ((LO.FirstOrder.Rew.map mapping id).q ▹ body) =
          nnfPrincipalSymbols body
      rw [LO.FirstOrder.Rew.q_map]
      exact inductionHypothesis (0 :> (Fin.succ ∘ mapping))
  | ex body inductionHypothesis =>
      change
        nnfPrincipalSymbols
            ((LO.FirstOrder.Rew.map mapping id).q ▹ body) =
          nnfPrincipalSymbols body
      rw [LO.FirstOrder.Rew.q_map]
      exact inductionHypothesis (0 :> (Fin.succ ∘ mapping))

theorem termPrincipalSymbols_bShift_exact {depth : Nat}
    (term : LO.FirstOrder.Semiterm language Empty depth) :
    termPrincipalSymbols (LO.FirstOrder.Rew.bShift term) =
      termPrincipalSymbols term :=
  termPrincipalSymbols_map_exact Fin.succ term

theorem nnfPrincipalSymbols_bShift_exact {depth : Nat}
    (formula : Formula depth) :
    nnfPrincipalSymbols (LO.FirstOrder.Rew.bShift ▹ formula) =
      nnfPrincipalSymbols formula :=
  nnfPrincipalSymbols_map_exact Fin.succ formula

theorem PrenexForm.principalSymbols_rew_bShift_exact {depth : Nat}
    (form : PrenexForm depth) :
    nnfPrincipalSymbols
        (form.rew LO.FirstOrder.Rew.bShift).toFormula =
      nnfPrincipalSymbols form.toFormula := by
  rw [form.rew_toFormula_exact]
  exact nnfPrincipalSymbols_bShift_exact form.toFormula

/-- Prefix combination preserves the Boolean connective exactly.  The
nonempty-domain hypothesis is the standard first-order convention needed when
an existential is pulled across a constant true disjunct (and dually for
universal conjunction). -/
theorem combine_eval_exact {Domain : Type} [Nonempty Domain]
    (interpretation : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (environment : Fin depth -> Domain)
    (connective : Connective) (left right : PrenexForm depth) :
    Eval interpretation environment (combine connective left right).toFormula <->
      connective.holds
        (Eval interpretation environment left.toFormula)
        (Eval interpretation environment right.toFormula) := by
  cases left with
  | all leftBody =>
      simp only [combine, PrenexForm.toFormula,
        Eval, LO.FirstOrder.Semiformula.EvalAux]
      calc
        (forall value,
            Eval interpretation (value :> environment)
              (combine connective leftBody
                (right.rew LO.FirstOrder.Rew.bShift)).toFormula) <->
            (forall value,
              connective.holds
                (Eval interpretation (value :> environment) leftBody.toFormula)
                (Eval interpretation (value :> environment)
                  (right.rew LO.FirstOrder.Rew.bShift).toFormula)) :=
          forall_congr' fun value =>
            combine_eval_exact interpretation (value :> environment)
              connective leftBody (right.rew LO.FirstOrder.Rew.bShift)
        _ <->
            (forall value,
              connective.holds
                (Eval interpretation (value :> environment) leftBody.toFormula)
                (Eval interpretation environment right.toFormula)) :=
          forall_congr' fun value =>
            connective.holds_congr Iff.rfl
              (right.eval_rew_bShift_exact interpretation environment value)
        _ <->
            connective.holds
              (forall value,
                Eval interpretation (value :> environment) leftBody.toFormula)
              (Eval interpretation environment right.toFormula) :=
          forall_connective_left connective _ _
  | ex leftBody =>
      simp only [combine, PrenexForm.toFormula,
        Eval, LO.FirstOrder.Semiformula.EvalAux]
      calc
        (exists value,
            Eval interpretation (value :> environment)
              (combine connective leftBody
                (right.rew LO.FirstOrder.Rew.bShift)).toFormula) <->
            (exists value,
              connective.holds
                (Eval interpretation (value :> environment) leftBody.toFormula)
                (Eval interpretation (value :> environment)
                  (right.rew LO.FirstOrder.Rew.bShift).toFormula)) :=
          exists_congr fun value =>
            combine_eval_exact interpretation (value :> environment)
              connective leftBody (right.rew LO.FirstOrder.Rew.bShift)
        _ <->
            (exists value,
              connective.holds
                (Eval interpretation (value :> environment) leftBody.toFormula)
                (Eval interpretation environment right.toFormula)) :=
          exists_congr fun value =>
            connective.holds_congr Iff.rfl
              (right.eval_rew_bShift_exact interpretation environment value)
        _ <->
            connective.holds
              (exists value,
                Eval interpretation (value :> environment) leftBody.toFormula)
              (Eval interpretation environment right.toFormula) :=
          exists_connective_left connective _ _
  | matrix leftFormula leftQf =>
      cases right with
      | all rightBody =>
          simp only [combine, PrenexForm.toFormula,
            Eval, LO.FirstOrder.Semiformula.EvalAux]
          calc
            (forall value,
                Eval interpretation (value :> environment)
                  (combine connective
                    ((PrenexForm.matrix leftFormula leftQf).rew
                      LO.FirstOrder.Rew.bShift)
                    rightBody).toFormula) <->
                (forall value,
                  connective.holds
                    (Eval interpretation (value :> environment)
                      ((PrenexForm.matrix leftFormula leftQf).rew
                        LO.FirstOrder.Rew.bShift).toFormula)
                    (Eval interpretation (value :> environment)
                      rightBody.toFormula)) :=
              forall_congr' fun value =>
                combine_eval_exact interpretation (value :> environment)
                  connective
                  ((PrenexForm.matrix leftFormula leftQf).rew
                    LO.FirstOrder.Rew.bShift)
                  rightBody
            _ <->
                (forall value,
                  connective.holds
                    (Eval interpretation environment leftFormula)
                    (Eval interpretation (value :> environment)
                      rightBody.toFormula)) :=
              forall_congr' fun value =>
                connective.holds_congr
                  ((PrenexForm.matrix leftFormula leftQf).eval_rew_bShift_exact
                    interpretation environment value)
                  Iff.rfl
            _ <->
                connective.holds
                  (Eval interpretation environment leftFormula)
                  (forall value,
                    Eval interpretation (value :> environment)
                      rightBody.toFormula) :=
              forall_connective_right connective _ _
      | ex rightBody =>
          simp only [combine, PrenexForm.toFormula,
            Eval, LO.FirstOrder.Semiformula.EvalAux]
          calc
            (exists value,
                Eval interpretation (value :> environment)
                  (combine connective
                    ((PrenexForm.matrix leftFormula leftQf).rew
                      LO.FirstOrder.Rew.bShift)
                    rightBody).toFormula) <->
                (exists value,
                  connective.holds
                    (Eval interpretation (value :> environment)
                      ((PrenexForm.matrix leftFormula leftQf).rew
                        LO.FirstOrder.Rew.bShift).toFormula)
                    (Eval interpretation (value :> environment)
                      rightBody.toFormula)) :=
              exists_congr fun value =>
                combine_eval_exact interpretation (value :> environment)
                  connective
                  ((PrenexForm.matrix leftFormula leftQf).rew
                    LO.FirstOrder.Rew.bShift)
                  rightBody
            _ <->
                (exists value,
                  connective.holds
                    (Eval interpretation environment leftFormula)
                    (Eval interpretation (value :> environment)
                      rightBody.toFormula)) :=
              exists_congr fun value =>
                connective.holds_congr
                  ((PrenexForm.matrix leftFormula leftQf).eval_rew_bShift_exact
                    interpretation environment value)
                  Iff.rfl
            _ <->
                connective.holds
                  (Eval interpretation environment leftFormula)
                  (exists value,
                    Eval interpretation (value :> environment)
                      rightBody.toFormula) :=
              exists_connective_right connective _ _
      | matrix rightFormula rightQf =>
          cases connective <;>
            simp [combine, Connective.apply, Connective.holds,
              PrenexForm.toFormula, Eval,
              LO.FirstOrder.Semiformula.EvalAux]
termination_by left.quantifierCount + right.quantifierCount
decreasing_by
  all_goals
    simp_all [PrenexForm.quantifierCount,
      PrenexForm.rew_quantifierCount_exact]

theorem combine_principalSymbols_exact {depth : Nat}
    (connective : Connective) (left right : PrenexForm depth) :
    nnfPrincipalSymbols (combine connective left right).toFormula =
      nnfPrincipalSymbols left.toFormula ∪
        nnfPrincipalSymbols right.toFormula := by
  cases left with
  | all leftBody =>
      simp only [combine, PrenexForm.toFormula, nnfPrincipalSymbols]
      rw [combine_principalSymbols_exact]
      rw [right.principalSymbols_rew_bShift_exact]
  | ex leftBody =>
      simp only [combine, PrenexForm.toFormula, nnfPrincipalSymbols]
      rw [combine_principalSymbols_exact]
      rw [right.principalSymbols_rew_bShift_exact]
  | matrix leftFormula leftQf =>
      cases right with
      | all rightBody =>
          simp only [combine, PrenexForm.toFormula, nnfPrincipalSymbols]
          rw [combine_principalSymbols_exact]
          rw [(PrenexForm.matrix leftFormula leftQf).principalSymbols_rew_bShift_exact]
          rfl
      | ex rightBody =>
          simp only [combine, PrenexForm.toFormula, nnfPrincipalSymbols]
          rw [combine_principalSymbols_exact]
          rw [(PrenexForm.matrix leftFormula leftQf).principalSymbols_rew_bShift_exact]
          rfl
      | matrix rightFormula rightQf =>
          cases connective <;>
            simp [combine, Connective.apply, PrenexForm.toFormula,
              nnfPrincipalSymbols]
termination_by left.quantifierCount + right.quantifierCount
decreasing_by
  all_goals
    simp_all [PrenexForm.quantifierCount,
      PrenexForm.rew_quantifierCount_exact]

/-- Total prenex normalization of canonical NNF. -/
def prenex {depth : Nat} : Formula depth -> PrenexForm depth
  | .verum => .matrix .verum trivial
  | .falsum => .matrix .falsum trivial
  | .rel relation arguments => .matrix (.rel relation arguments) trivial
  | .nrel relation arguments => .matrix (.nrel relation arguments) trivial
  | .and left right => combine .and (prenex left) (prenex right)
  | .or left right => combine .or (prenex left) (prenex right)
  | .all body => .all (prenex body)
  | .ex body => .ex (prenex body)

/-- The total prenex construction preserves truth in every nonempty
first-order structure and under every bound-variable environment. -/
theorem prenex_eval_exact {Domain : Type} [Nonempty Domain]
    (interpretation : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (environment : Fin depth -> Domain)
    (formula : Formula depth) :
    Eval interpretation environment (prenex formula).toFormula <->
      Eval interpretation environment formula := by
  induction formula with
  | verum => rfl
  | falsum => rfl
  | rel => rfl
  | nrel => rfl
  | and left right leftHypothesis rightHypothesis =>
      exact
        (combine_eval_exact interpretation environment .and
          (prenex left) (prenex right)).trans
        (Connective.holds_congr .and
          (leftHypothesis environment) (rightHypothesis environment))
  | or left right leftHypothesis rightHypothesis =>
      exact
        (combine_eval_exact interpretation environment .or
          (prenex left) (prenex right)).trans
        (Connective.holds_congr .or
          (leftHypothesis environment) (rightHypothesis environment))
  | all body inductionHypothesis =>
      simpa only [prenex, PrenexForm.toFormula, Eval,
        LO.FirstOrder.Semiformula.EvalAux] using
        (forall_congr' fun value =>
          inductionHypothesis (value :> environment))
  | ex body inductionHypothesis =>
      simpa only [prenex, PrenexForm.toFormula, Eval,
        LO.FirstOrder.Semiformula.EvalAux] using
        (exists_congr fun value =>
          inductionHypothesis (value :> environment))

theorem prenex_principalSymbols_exact {depth : Nat}
    (formula : Formula depth) :
    nnfPrincipalSymbols (prenex formula).toFormula =
      nnfPrincipalSymbols formula := by
  induction formula with
  | verum => rfl
  | falsum => rfl
  | rel => rfl
  | nrel => rfl
  | and left right leftHypothesis rightHypothesis =>
      rw [prenex, combine_principalSymbols_exact,
        leftHypothesis, rightHypothesis]
      rfl
  | or left right leftHypothesis rightHypothesis =>
      rw [prenex, combine_principalSymbols_exact,
        leftHypothesis, rightHypothesis]
      rfl
  | all body inductionHypothesis =>
      simpa only [prenex, PrenexForm.toFormula,
        nnfPrincipalSymbols] using inductionHypothesis
  | ex body inductionHypothesis =>
      simpa only [prenex, PrenexForm.toFormula,
        nnfPrincipalSymbols] using inductionHypothesis

def normalize {depth : Nat} (formula : Formula depth) : Formula depth :=
  (prenex formula).toFormula

theorem normalize_prenex {depth : Nat} (formula : Formula depth) :
    Prenex (normalize formula) :=
  (prenex formula).toFormula_prenex

theorem normalize_eval_exact {Domain : Type} [Nonempty Domain]
    (interpretation : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (environment : Fin depth -> Domain)
    (formula : Formula depth) :
    Eval interpretation environment (normalize formula) <->
      Eval interpretation environment formula :=
  prenex_eval_exact interpretation environment formula

theorem normalize_principalSymbols_exact {depth : Nat}
    (formula : Formula depth) :
    nnfPrincipalSymbols (normalize formula) =
      nnfPrincipalSymbols formula :=
  prenex_principalSymbols_exact formula

namespace Canary

def p : PredicateSymbol 1 := ⟨"p", .plain⟩
def q : PredicateSymbol 1 := ⟨"q", .plain⟩

/-- Both branches begin with a quantifier, so the input is NNF but not
prenex. -/
def source : Formula 0 :=
  .or
    (.ex (.rel (.predicate p) ![.bvar 0]))
    (.all (.rel (.predicate q) ![.bvar 0]))

theorem source_not_prenex : Not (Prenex source) := by
  intro claimed
  cases claimed with
  | matrix quantifierFree =>
      simp [source, QuantifierFree] at quantifierFree

/-- The left prefix is retained first.  Shifting the left matrix under the
right universal changes its bound occurrence from index zero to index one,
which is the capture-avoidance canary. -/
theorem source_normalizes_exactly :
    normalize source =
      .ex (.all
        (.or
          (.rel (.predicate p) ![.bvar 1])
          (.rel (.predicate q) ![.bvar 0]))) := by
  simp [normalize, source, prenex, combine, Connective.apply,
    PrenexForm.toFormula, PrenexForm.rew,
    LO.FirstOrder.Semiformula.rew_rel, Matrix.constant_eq_singleton]

theorem source_output_is_prenex : Prenex (normalize source) :=
  normalize_prenex source

theorem source_semantics_exact {Domain : Type} [Nonempty Domain]
    (interpretation : LO.FirstOrder.Structure language Domain) :
    Eval interpretation ![] (normalize source) <->
      Eval interpretation ![] source :=
  normalize_eval_exact interpretation ![] source

theorem source_principalSymbols_exact :
    nnfPrincipalSymbols (normalize source) =
      nnfPrincipalSymbols source :=
  normalize_principalSymbols_exact source

end Canary

#print axioms combine_eval_exact
#print axioms normalize_eval_exact
#print axioms normalize_principalSymbols_exact
#print axioms Canary.source_semantics_exact

end Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics
