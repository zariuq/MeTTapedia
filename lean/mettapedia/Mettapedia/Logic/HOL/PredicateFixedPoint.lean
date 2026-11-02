import Mettapedia.Logic.HOL.ProofSyntaxStructural
import Mettapedia.Logic.HOL.TermInterpretationLaws

/-!
# Least predicate fixed points with retained HOL proofs

Predicate inclusion, operator monotonicity and least prefixed predicates are
object-language HOL formulas. The proof constructors below retain the actual
quantifier, implication and beta steps. No datatype induction law is assumed.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.PredicateFixedPoint
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
variable {α : Ty Base}
abbrev Predicate (α : Ty Base) := α ⇒ .prop
abbrev Operator (α : Ty Base) := Predicate α ⇒ Predicate α

def included (left right : Term Const Γ (Predicate α)) : Formula Const Γ :=
  .all (.imp (.app (weaken left) (.var .vz)) (.app (weaken right) (.var .vz)))

def prefixed (operator : Term Const Γ (Operator α))
    (property : Term Const Γ (Predicate α)) : Formula Const Γ :=
  included (.app operator property) property

def monotone (operator : Term Const Γ (Operator α)) : Formula Const Γ :=
  .all (.all (.imp (included (.var (.vs .vz)) (.var .vz))
    (included (.app (weaken (weaken operator)) (.var (.vs .vz)))
      (.app (weaken (weaken operator)) (.var .vz)))))

def leastBody (operator : Term Const Γ (Operator α))
    (point : Term Const Γ α) : Formula Const Γ :=
  .all (.imp (prefixed (weaken operator) (.var .vz))
    (.app (.var .vz) (weaken point)))

def least (operator : Term Const Γ (Operator α)) : Term Const Γ (Predicate α) :=
  .lam (leastBody (weaken operator) (.var .vz))

section Reading
universe u' v'
variable {Target : Type u'} {Symbols : Ty Target → Type v'}
  (reading : TermInterpretation Base Const Target Symbols)

@[simp] theorem read_included (left right : Term Const Γ (Predicate α)) :
    reading.term (included left right) = included (reading.term left) (reading.term right) := by
  simp [included, Var.mapTypes]

@[simp] theorem read_prefixed (operator : Term Const Γ (Operator α)) (property : Term Const Γ (Predicate α)) :
    reading.term (prefixed operator property) = prefixed (reading.term operator) (reading.term property) := by
  simp [prefixed]

@[simp] theorem read_leastBody (operator : Term Const Γ (Operator α)) (point : Term Const Γ α) :
    reading.term (leastBody operator point) = leastBody (reading.term operator) (reading.term point) := by
  simp [leastBody, Var.mapTypes]
  rfl

@[simp] theorem read_least (operator : Term Const Γ (Operator α)) :
    reading.term (least operator) = least (reading.term operator) := by
  simp [least, Var.mapTypes]

end Reading

@[simp] theorem rename_included {Γ' : Ctx Base} (ρ : Rename Base Γ Γ')
    (left right : Term Const Γ (Predicate α)) :
    HOL.rename ρ (included left right) = included (HOL.rename ρ left) (HOL.rename ρ right) := by
  simp [included, HOL.rename, Rename.lift]

@[simp] theorem rename_prefixed {Γ' : Ctx Base} (ρ : Rename Base Γ Γ')
    (operator : Term Const Γ (Operator α)) (property : Term Const Γ (Predicate α)) :
    HOL.rename ρ (prefixed operator property) =
      prefixed (HOL.rename ρ operator) (HOL.rename ρ property) := by
  simp [prefixed, HOL.rename]

@[simp] theorem rename_leastBody {Γ' : Ctx Base} (ρ : Rename Base Γ Γ')
    (operator : Term Const Γ (Operator α)) (point : Term Const Γ α) :
    HOL.rename ρ (leastBody operator point) =
      leastBody (HOL.rename ρ operator) (HOL.rename ρ point) := by
  simp [leastBody, HOL.rename, Rename.lift]

@[simp] theorem rename_least {Γ' : Ctx Base} (ρ : Rename Base Γ Γ')
    (operator : Term Const Γ (Operator α)) :
    HOL.rename ρ (least operator) = least (HOL.rename ρ operator) := by
  simp [least, HOL.rename, Rename.lift]

@[simp] theorem rename_monotone {Γ' : Ctx Base} (ρ : Rename Base Γ Γ')
    (operator : Term Const Γ (Operator α)) :
    HOL.rename ρ (monotone operator) = monotone (HOL.rename ρ operator) := by
  simp [monotone, HOL.rename, Rename.lift]

@[simp] theorem subst_included {Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    (left right : Term Const Γ (Predicate α)) :
    HOL.subst θ (included left right) = included (HOL.subst θ left) (HOL.subst θ right) := by
  simp [included, HOL.subst, Subst.lift]

@[simp] theorem subst_prefixed {Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    (operator : Term Const Γ (Operator α)) (property : Term Const Γ (Predicate α)) :
    HOL.subst θ (prefixed operator property) =
      prefixed (HOL.subst θ operator) (HOL.subst θ property) := by
  simp [prefixed, HOL.subst]

@[simp] theorem subst_leastBody {Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    (operator : Term Const Γ (Operator α)) (point : Term Const Γ α) :
    HOL.subst θ (leastBody operator point) =
      leastBody (HOL.subst θ operator) (HOL.subst θ point) := by
  simp [leastBody, HOL.subst, Subst.lift]

@[simp] theorem subst_least {Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    (operator : Term Const Γ (Operator α)) :
    HOL.subst θ (least operator) = least (HOL.subst θ operator) := by
  simp [least, HOL.subst, Subst.lift]

@[simp] theorem subst_single_weaken {σ τ : Ty Base}
    (argument : Term Const Γ σ) (term : Term Const Γ τ) :
    HOL.subst (Subst.single argument) (weaken term) = term :=
  instantiate_weaken argument term

@[simp] theorem instantiate_included (point : Term Const Γ α)
    (left right : Term Const Γ (Predicate α)) :
    instantiate point
      (.imp (.app (weaken left) (.var .vz)) (.app (weaken right) (.var .vz))) =
      .imp (.app left point) (.app right point) := by
  simp only [instantiate, HOL.subst]
  rw [← instantiate, instantiate_weaken, ← instantiate, instantiate_weaken]
  rfl

variable {Δ : List (Formula Const Γ)}

def weakenProof {σ : Ty Base} {formula : Formula Const Γ}
    (proof : ProofSyntax Const Δ formula) :
    ProofSyntax Const (weakenHyps (σ := σ) Δ) (weaken formula) :=
  ProofSyntax.castIndices
    (by apply List.map_congr_left; intro item _; rfl) rfl
    (ProofSyntax.rename (Rename.weaken (σ := σ)) proof)

def inclusion_elim (left right : Term Const Γ (Predicate α)) (point : Term Const Γ α)
    (inclusion : ProofSyntax Const Δ (included left right))
    (member : ProofSyntax Const Δ (.app left point)) :
    ProofSyntax Const Δ (.app right point) := by
  have implication : ProofSyntax Const Δ (.imp (.app left point) (.app right point)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.allE point inclusion)
    simp only [instantiate_included]
  exact .impE implication member

def least_beta (operator : Term Const Γ (Operator α)) (point : Term Const Γ α) :
    ProofSyntax Const Δ (.eq (.app (least operator) point) (leastBody operator point)) := by
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.beta (Δ := Δ) point (leastBody (weaken operator) (.var .vz)))
  simp [least, instantiate, subst_leastBody, HOL.subst, Subst.single]

def least_elim (operator : Term Const Γ (Operator α))
    (property : Term Const Γ (Predicate α)) (point : Term Const Γ α)
    (member : ProofSyntax Const Δ (.app (least operator) point))
    (closed : ProofSyntax Const Δ (prefixed operator property)) :
    ProofSyntax Const Δ (.app property point) := by
  have unfolded : ProofSyntax Const Δ (leastBody operator point) :=
    .impE (.eqPropEL (least_beta operator point)) member
  have implication : ProofSyntax Const Δ
      (.imp (prefixed operator property) (.app property point)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.allE property unfolded)
    simp [instantiate, subst_prefixed, HOL.subst, Subst.single]
  exact .impE implication closed

def minimality (operator : Term Const Γ (Operator α))
    (property : Term Const Γ (Predicate α)) :
    ProofSyntax Const Δ (.imp (prefixed operator property) (included (least operator) property)) := by
  refine .impI (.allI (.impI ?_))
  have member : ProofSyntax Const
      (.app (weaken (least operator)) (.var .vz) ::
        weakenHyps (prefixed operator property :: Δ))
      (.app (least (weaken operator)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.hyp (Const := Const)
        (Δ := .app (weaken (least operator)) (.var .vz) ::
          weakenHyps (prefixed operator property :: Δ)) ⟨0, by simp⟩)
    simp [weaken, rename_least]
  have closed : ProofSyntax Const
      (.app (weaken (least operator)) (.var .vz) ::
        weakenHyps (prefixed operator property :: Δ))
      (prefixed (weaken operator) (weaken property)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.hyp (Const := Const)
        (Δ := .app (weaken (least operator)) (.var .vz) ::
          weakenHyps (prefixed operator property :: Δ)) ⟨1, by simp [weakenHyps]⟩)
    simp [weakenHyps, weaken, rename_prefixed]
  exact least_elim (weaken operator) (weaken property) (.var .vz) member closed

def monotonicity_elim (operator : Term Const Γ (Operator α))
    (left right : Term Const Γ (Predicate α))
    (order : ProofSyntax Const Δ (monotone operator))
    (inclusion : ProofSyntax Const Δ (included left right)) :
    ProofSyntax Const Δ (included (.app operator left) (.app operator right)) := by
  have first : ProofSyntax Const Δ
      (.all (.imp (included (weaken left) (.var .vz))
        (included (.app (weaken operator) (weaken left))
          (.app (weaken operator) (.var .vz))))) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.allE left order)
    simp only [instantiate, subst_included, HOL.subst, Subst.lift]
    simp [Subst.single]
    exact ⟨rfl, rfl⟩
  have implication : ProofSyntax Const Δ
      (.imp (included left right) (included (.app operator left) (.app operator right))) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.allE right first)
    simp [instantiate, subst_included, HOL.subst, Subst.single]
  exact .impE implication inclusion

def least_intro (operator : Term Const Γ (Operator α)) (point : Term Const Γ α)
    (universal : ProofSyntax Const (weakenHyps Δ)
      (.imp (prefixed (weaken operator) (.var .vz))
        (.app (.var .vz) (weaken point)))) :
    ProofSyntax Const Δ (.app (least operator) point) :=
  .impE (.eqPropER (least_beta operator point)) (.allI universal)

/-- Monotonicity closes the intersection of all prefixed predicates. -/
def closure_at (operator : Term Const Γ (Operator α)) (point : Term Const Γ α)
    (order : ProofSyntax Const Δ (monotone operator))
    (imageMember : ProofSyntax Const Δ (.app (.app operator (least operator)) point)) :
    ProofSyntax Const Δ (.app (least operator) point) := by
  refine least_intro operator point (.impI ?_)
  let raised := weaken (σ := Predicate α) operator
  let property : Term Const (Predicate α :: Γ) (Predicate α) := .var .vz
  let assumptions := prefixed raised property :: weakenHyps (σ := Predicate α) Δ
  have closed : ProofSyntax Const assumptions (prefixed raised property) := .hyp ⟨0, by simp [assumptions]⟩
  have belowProperty : ProofSyntax Const assumptions (included (least raised) property) :=
    .impE (minimality raised property) closed
  have raisedOrder : ProofSyntax Const assumptions (monotone raised) := by
    apply ProofSyntax.castIndices rfl ?_
      ((weakenProof (σ := Predicate α) order).prepend (prefixed raised property))
    simp [raised, weaken, rename_monotone]
  have raisedMember : ProofSyntax Const assumptions
      (.app (.app raised (least raised)) (weaken point)) := by
    apply ProofSyntax.castIndices rfl ?_
      ((weakenProof (σ := Predicate α) imageMember).prepend (prefixed raised property))
    simp [raised, weaken, HOL.rename, rename_least]
  exact inclusion_elim (.app raised property) property (weaken point) closed
    (inclusion_elim (.app raised (least raised)) (.app raised property) (weaken point)
      (monotonicity_elim raised (least raised) property raisedOrder belowProperty) raisedMember)

def least_prefixed (operator : Term Const Γ (Operator α))
    (order : ProofSyntax Const Δ (monotone operator)) :
    ProofSyntax Const Δ (prefixed operator (least operator)) := by
  refine .allI (.impI ?_)
  let premise : Formula Const (α :: Γ) :=
    .app (.app (weaken operator) (weaken (least operator))) (.var .vz)
  have raisedOrder : ProofSyntax Const (premise :: weakenHyps Δ) (monotone (weaken operator)) := by
    apply ProofSyntax.castIndices rfl ?_ ((weakenProof (σ := α) order).prepend premise)
    simp [weaken, rename_monotone]
  have member : ProofSyntax Const (premise :: weakenHyps Δ)
      (.app (.app (weaken operator) (least (weaken operator))) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.hyp (Const := Const) (Δ := premise :: weakenHyps Δ) ⟨0, by simp⟩)
    simp [premise, weaken, rename_least]
  apply ProofSyntax.castIndices ?_ ?_ (closure_at (weaken operator) (.var .vz) raisedOrder member)
  · simp [premise, weaken, HOL.rename]
  · simp [weaken, rename_least]

/-- The least prefixed predicate is also postfixed; both directions are retained. -/
def least_postfixed (operator : Term Const Γ (Operator α))
    (order : ProofSyntax Const Δ (monotone operator)) :
    ProofSyntax Const Δ (included (least operator) (.app operator (least operator))) := by
  have imageClosed : ProofSyntax Const Δ (prefixed operator (.app operator (least operator))) :=
    monotonicity_elim operator (.app operator (least operator)) (least operator) order
      (least_prefixed operator order)
  exact .impE (minimality operator (.app operator (least operator))) imageClosed

def equation (operator : Term Const Γ (Operator α)) : Formula Const Γ :=
  .all (.eq (.app (weaken (least operator)) (.var .vz))
    (.app (weaken (.app operator (least operator))) (.var .vz)))

def fixed_point (operator : Term Const Γ (Operator α))
    (order : ProofSyntax Const Δ (monotone operator)) : ProofSyntax Const Δ (equation operator) := by
  have forward : ProofSyntax Const (weakenHyps (σ := α) Δ)
      (included (weaken (least operator)) (weaken (.app operator (least operator)))) := by
    apply ProofSyntax.castIndices rfl ?_ (weakenProof (σ := α) (least_postfixed operator order))
    simp only [weaken, rename_included]
  have backward : ProofSyntax Const (weakenHyps (σ := α) Δ)
      (included (weaken (.app operator (least operator))) (weaken (least operator))) := by
    apply ProofSyntax.castIndices rfl ?_ (weakenProof (σ := α) (least_prefixed operator order))
    simp only [prefixed, weaken, rename_included]
  refine .allI (.eqPropI ?_ ?_)
  · apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.allE (.var .vz) forward)
    simp only [instantiate_included]
  · apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.allE (.var .vz) backward)
    simp only [instantiate_included]

/-- Induction into any prefixed predicate, with both operator and predicate quantified. -/
def induction_schema (α : Ty Base) :
    ProofSyntax Const ([] : List (Formula Const []))
      (.all (.all (.imp
        (prefixed (.var (.vs .vz) : Term Const [Predicate α, Operator α] (Operator α)) (.var .vz))
        (included (least (.var (.vs .vz))) (.var .vz))))) :=
  .allI (.allI (minimality (.var (.vs .vz)) (.var .vz)))

/-- A native-exportable logical schema; the operator itself remains quantified. -/
def fixed_point_schema (α : Ty Base) :
    ProofSyntax Const ([] : List (Formula Const []))
      (.all (.imp (monotone (.var .vz : Term Const [Operator α] (Operator α)))
        (equation (.var .vz)))) :=
  .allI (.impI (fixed_point (.var .vz) (.hyp ⟨0, by simp⟩)))

set_option backward.isDefEq.respectTransparency false in
/-- The fixed-point program needs no function-extensionality or eta rule. -/
theorem fixed_point_schema_functionExtensionalityFree (α : Ty Base) :
    ProofSyntax.FunctionExtensionalityFree (fixed_point_schema (Const := Const) α) := by
  simp [fixed_point_schema, fixed_point, least_postfixed, least_prefixed, closure_at,
    least_intro, monotonicity_elim, minimality, least_elim, least_beta, inclusion_elim,
    weakenProof, ProofSyntax.prepend, ProofSyntax.FunctionExtensionalityFree]

set_option backward.isDefEq.respectTransparency false in
/-- The induction program uses only the same intensional logical rules. -/
theorem induction_schema_functionExtensionalityFree (α : Ty Base) :
    ProofSyntax.FunctionExtensionalityFree (induction_schema (Const := Const) α) := by
  simp [induction_schema, minimality, least_elim, least_beta,
    ProofSyntax.FunctionExtensionalityFree]

#print axioms fixed_point_schema
#print axioms induction_schema
end Mettapedia.Logic.HOL.PredicateFixedPoint
