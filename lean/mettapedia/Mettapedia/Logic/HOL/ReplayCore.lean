import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties
import Mettapedia.Logic.HOL.Semantics.KripkeHenkin

/-!
# Certificate replay as a higher-order theory

A raw certificate is a finite tree of rule labels.  Replay checks it against a
goal: the root label determines ordered premises and a conclusion, the
conclusion must be the goal, and the children are checked against the
premises in order.  This module presents that replay core as a theory of
Church-style higher-order logic in the deep embedding, and derives its
soundness inside the object logic.

**Signature.**  Five sorts: goals, rule labels, certificates, certificate
lists and goal lists.
* `node`, `nil` and `cons` build certificates and their child lists;
  `goalsNil` and `goalsCons` build premise lists, which replay destructures
  in step with the child lists.
* `rule l ps g`: the label `l` concludes `g` from the ordered premises `ps`.
  It is the graph of the local rule map, read as a relation because the
  signature has no option or product types.
* `acc g c`: replay accepts the certificate `c` for the goal `g`; `accs` is
  its pointwise extension to lists, failing on a length mismatch.
* `der g`: the goal `g` is derivable; `ders` extends it to every goal of a
  list.  Derivations are read as a predicate on goals, with proof terms
  erased.

**Axioms.**  Seven sentences, each the reading of one defining clause of the
replay core:
* the recursion equations of acceptance, with equality at type `prop` as the
  biconditional: at a node (`accNode`), at the empty child list (`accsNil`),
  and at a nonempty child list (`accsCons`);
* the closure rules of derivability: the constructors of derivation trees
  (`derRule`, `dersNil`, `dersCons`);
* induction on certificates (`certInduction`): one sentence quantifying over
  a predicate on certificates and a predicate on certificate lists.  It is
  the recursor of the nested inductive type of certificates at propositional
  motives, i.e. the initial-algebra property of finite certificate trees.

**The derivation.**  `soundness_derivation` derives `∀ c g. acc g c → der g`
from the seven axioms in the extensional calculus `ExtDerivation`, by one
application of the induction axiom to two λ-predicates (`certClaim`,
`certsClaim`).  The proof uses only assumptions, implication, the universal
quantifier, conjunction elimination, existential elimination, β-conversion,
argument congruence of equality, and the use of an equation between
propositions as an implication: no excluded middle, no choice or description
operator (the signature has none), and no extensionality rule.  The
derivation is therefore intuitionistic, and `soundness_kripkeConsequence`
states it semantically: the target holds at every world of every
substitutional Kripke–Henkin structure forcing the seven axioms.

**Junk model.**  `JunkModel` validates the six recursion and closure axioms,
but its certificates contain a cyclic certificate: a node whose only child is
itself.  The cycle is accepted for the one goal, no goal is derivable, the
induction sentence fails and so does soundness.  Hence
`clauses_do_not_derive_soundness`: without the induction axiom the six
clauses do not derive soundness.

Standard models over concrete certificate types are given where those types
are defined.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ReplayCore

universe w

/-- The five sorts of the replay core. -/
inductive BaseSort where
  | goal
  | label
  | cert
  | certs
  | goals

abbrev goal : Ty BaseSort := .base .goal
abbrev label : Ty BaseSort := .base .label
abbrev cert : Ty BaseSort := .base .cert
abbrev certs : Ty BaseSort := .base .certs
abbrev goals : Ty BaseSort := .base .goals
/-- Predicates on certificates. -/
abbrev certPredicate : Ty BaseSort := cert ⇒ .prop
/-- Predicates on certificate lists. -/
abbrev certsPredicate : Ty BaseSort := certs ⇒ .prop

/-- The constants of the replay core. -/
inductive Symbol : Ty BaseSort → Type where
  | node : Symbol (label ⇒ certs ⇒ cert)
  | nil : Symbol certs
  | cons : Symbol (cert ⇒ certs ⇒ certs)
  | goalsNil : Symbol goals
  | goalsCons : Symbol (goal ⇒ goals ⇒ goals)
  | rule : Symbol (label ⇒ goals ⇒ goal ⇒ .prop)
  | acc : Symbol (goal ⇒ cert ⇒ .prop)
  | accs : Symbol (goals ⇒ certs ⇒ .prop)
  | der : Symbol (goal ⇒ .prop)
  | ders : Symbol (goals ⇒ .prop)

abbrev Expr (Γ : Ctx BaseSort) (τ : Ty BaseSort) := Term Symbol Γ τ
abbrev Sentence (Γ : Ctx BaseSort) := Formula Symbol Γ

variable {Γ : Ctx BaseSort}

/-! ## Terms and atomic formulas -/

def node (l : Expr Γ label) (cs : Expr Γ certs) : Expr Γ cert :=
  .app (.app (.const .node) l) cs
def nil : Expr Γ certs := .const .nil
def cons (c : Expr Γ cert) (cs : Expr Γ certs) : Expr Γ certs :=
  .app (.app (.const .cons) c) cs
def goalsNil : Expr Γ goals := .const .goalsNil
def goalsCons (g : Expr Γ goal) (gs : Expr Γ goals) : Expr Γ goals :=
  .app (.app (.const .goalsCons) g) gs
def rule (l : Expr Γ label) (ps : Expr Γ goals) (g : Expr Γ goal) : Sentence Γ :=
  .app (.app (.app (.const .rule) l) ps) g
def acc (g : Expr Γ goal) (c : Expr Γ cert) : Sentence Γ :=
  .app (.app (.const .acc) g) c
def accs (ps : Expr Γ goals) (cs : Expr Γ certs) : Sentence Γ :=
  .app (.app (.const .accs) ps) cs
def der (g : Expr Γ goal) : Sentence Γ := .app (.const .der) g
def ders (ps : Expr Γ goals) : Sentence Γ := .app (.const .ders) ps

section Variables

variable {σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ : Ty BaseSort}

/-- The innermost bound variable. -/
abbrev v0 : Expr (σ₀ :: Γ) σ₀ := .var .vz
/-- The second bound variable, counting outwards. -/
abbrev v1 : Expr (σ₀ :: σ₁ :: Γ) σ₁ := .var (.vs .vz)
/-- The third bound variable, counting outwards. -/
abbrev v2 : Expr (σ₀ :: σ₁ :: σ₂ :: Γ) σ₂ := .var (.vs (.vs .vz))
/-- The fourth bound variable, counting outwards. -/
abbrev v3 : Expr (σ₀ :: σ₁ :: σ₂ :: σ₃ :: Γ) σ₃ := .var (.vs (.vs (.vs .vz)))
/-- The fifth bound variable, counting outwards. -/
abbrev v4 : Expr (σ₀ :: σ₁ :: σ₂ :: σ₃ :: σ₄ :: Γ) σ₄ :=
  .var (.vs (.vs (.vs (.vs .vz))))
/-- The sixth bound variable, counting outwards. -/
abbrev v5 : Expr (σ₀ :: σ₁ :: σ₂ :: σ₃ :: σ₄ :: σ₅ :: Γ) σ₅ :=
  .var (.vs (.vs (.vs (.vs (.vs .vz)))))

end Variables

/-! ## The seven axioms -/

/-- `∀ l cs g. acc g (node l cs) = ∃ ps. rule l ps g ∧ accs ps cs`. -/
def accNode : Sentence Γ :=
  .all (σ := label) (.all (σ := certs) (.all (σ := goal)
    (.eq (acc v0 (node v2 v1))
      (.ex (σ := goals) (.and (rule v3 v0 v1) (accs v0 v2))))))

/-- `∀ ps. accs ps nil = (ps = goalsNil)`. -/
def accsNil : Sentence Γ :=
  .all (σ := goals) (.eq (accs v0 nil) (.eq v0 goalsNil))

/-- `∀ c cs ps. accs ps (cons c cs) = ∃ g gs. ps = goalsCons g gs ∧ acc g c ∧ accs gs cs`. -/
def accsCons : Sentence Γ :=
  .all (σ := cert) (.all (σ := certs) (.all (σ := goals)
    (.eq (accs v0 (cons v2 v1))
      (.ex (σ := goal) (.ex (σ := goals)
        (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3))))))))

/-- `∀ l ps g. rule l ps g → ders ps → der g`. -/
def derRule : Sentence Γ :=
  .all (σ := label) (.all (σ := goals) (.all (σ := goal)
    (.imp (rule v2 v1 v0) (.imp (ders v1) (der v0)))))

/-- `ders goalsNil`. -/
def dersNil : Sentence Γ := ders goalsNil

/-- `∀ g gs. der g → ders gs → ders (goalsCons g gs)`. -/
def dersCons : Sentence Γ :=
  .all (σ := goal) (.all (σ := goals)
    (.imp (der v1) (.imp (ders v0) (ders (goalsCons v1 v0)))))

/-- `∀ l cs. Q cs → P (node l cs)`, for predicates `P` and `Q`. -/
def nodeClosed (P : Expr Γ certPredicate) (Q : Expr Γ certsPredicate) : Sentence Γ :=
  .all (σ := label) (.all (σ := certs)
    (.imp (.app (weaken (weaken Q)) v0) (.app (weaken (weaken P)) (node v1 v0))))

/-- `∀ c cs. P c → Q cs → Q (cons c cs)`, for predicates `P` and `Q`. -/
def consClosed (P : Expr Γ certPredicate) (Q : Expr Γ certsPredicate) : Sentence Γ :=
  .all (σ := cert) (.all (σ := certs)
    (.imp (.app (weaken (weaken P)) v1)
      (.imp (.app (weaken (weaken Q)) v0) (.app (weaken (weaken Q)) (cons v1 v0)))))

/-- Induction on certificates, one sentence of the object logic:
`∀ P Q. nodeClosed P Q → Q nil → consClosed P Q → ∀ c. P c`. -/
def certInduction : Sentence Γ :=
  .all (σ := certPredicate) (.all (σ := certsPredicate)
    (.imp (nodeClosed v1 v0)
      (.imp (.app v0 nil)
        (.imp (consClosed v1 v0) (.all (σ := cert) (.app v2 v0))))))

/-- The six recursion and closure clauses. -/
def clauses : List (Sentence Γ) := [accNode, accsNil, accsCons, derRule, dersNil, dersCons]

/-- The replay core: induction and the six clauses. -/
def theory : List (Sentence Γ) := certInduction :: clauses

/-- The target, soundness of replay: `∀ c g. acc g c → der g`. -/
def soundness : Sentence Γ :=
  .all (σ := cert) (.all (σ := goal) (.imp (acc v0 v1) (der v0)))

theorem mem_theory_certInduction : certInduction ∈ theory (Γ := Γ) := List.mem_cons_self
theorem mem_theory_accNode : accNode ∈ theory (Γ := Γ) :=
  List.mem_cons_of_mem _ List.mem_cons_self
theorem mem_theory_accsNil : accsNil ∈ theory (Γ := Γ) :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem mem_theory_accsCons : accsCons ∈ theory (Γ := Γ) :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem mem_theory_derRule : derRule ∈ theory (Γ := Γ) :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))
theorem mem_theory_dersNil : dersNil ∈ theory (Γ := Γ) :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
theorem mem_theory_dersCons : dersCons ∈ theory (Γ := Γ) :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))))

/-- The axioms are closed, so weakening the context leaves them unchanged. -/
@[simp] theorem weaken_theory {τ : Ty BaseSort} :
    weakenHyps (σ := τ) (theory (Γ := Γ)) = theory := rfl

/-! ## The derivation of soundness -/

/-- The certificate claim `λc. ∀g. acc g c → der g`. -/
def certClaim : Expr Γ certPredicate :=
  .lam (.all (σ := goal) (.imp (acc v0 v1) (der v0)))

/-- The list claim `λcs. ∀ps. accs ps cs → ders ps`. -/
def certsClaim : Expr Γ certsPredicate :=
  .lam (.all (σ := goals) (.imp (accs v0 v1) (ders v0)))

section Beta

variable {Δ : List (Sentence Γ)} {σ : Ty BaseSort} {body : Sentence (σ :: Γ)}
  {t : Expr Γ σ}

/-- An applied λ-predicate from its β-instance. -/
theorem lam_intro (h : ExtDerivation Symbol Δ (instantiate t body)) :
    ExtDerivation Symbol Δ (.app (.lam body) t) :=
  .impE (.eqPropER (.beta t body)) h

/-- The β-instance of an applied λ-predicate. -/
theorem lam_elim (h : ExtDerivation Symbol Δ (.app (.lam body) t)) :
    ExtDerivation Symbol Δ (instantiate t body) :=
  .impE (.eqPropEL (.beta t body)) h

end Beta

/-- Node case, innermost part.  In the context `g, cs, l`, acceptance of
`node l cs` for `g` and the list claim for `cs` derive `der g`: the node
equation yields premises `ps` with `rule l ps g` and `accs ps cs`, the list
claim yields `ders ps`, and the rule closure yields `der g`. -/
theorem node_case_body :
    ExtDerivation Symbol
      (acc v0 (node v2 v1) :: .app certsClaim v1 ::
        theory (Γ := goal :: certs :: label :: Γ))
      (der v0) := by
  have nodeAxiom : ExtDerivation Symbol
      (acc v0 (node v2 v1) :: .app certsClaim v1 ::
        theory (Γ := goal :: certs :: label :: Γ)) accNode :=
    ExtDerivation.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem_theory_accNode))
  have nodeEquation : ExtDerivation Symbol
      (acc v0 (node v2 v1) :: .app certsClaim v1 ::
        theory (Γ := goal :: certs :: label :: Γ))
      (.eq (acc v0 (node v2 v1)) (.ex (σ := goals) (.and (rule v3 v0 v1) (accs v0 v2)))) :=
    ExtDerivation.allE v0 (ExtDerivation.allE v1 (ExtDerivation.allE v2 nodeAxiom))
  have premisesExist := ExtDerivation.impE (ExtDerivation.eqPropEL nodeEquation)
    (ExtDerivation.hyp List.mem_cons_self)
  refine ExtDerivation.exE premisesExist ?_
  change ExtDerivation Symbol
    (.and (rule v3 v0 v1) (accs v0 v2) :: acc v1 (node v3 v2) :: .app certsClaim v2 ::
      theory (Γ := goals :: goal :: certs :: label :: Γ))
    (der v1)
  have premises : ExtDerivation Symbol
      (.and (rule v3 v0 v1) (accs v0 v2) :: acc v1 (node v3 v2) :: .app certsClaim v2 ::
        theory (Γ := goals :: goal :: certs :: label :: Γ))
      (.and (rule v3 v0 v1) (accs v0 v2)) :=
    ExtDerivation.hyp List.mem_cons_self
  have listClaim : ExtDerivation Symbol
      (.and (rule v3 v0 v1) (accs v0 v2) :: acc v1 (node v3 v2) :: .app certsClaim v2 ::
        theory (Γ := goals :: goal :: certs :: label :: Γ))
      (.all (σ := goals) (.imp (accs v0 v3) (ders v0))) :=
    lam_elim (ExtDerivation.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  have premisesDerivable : ExtDerivation Symbol
      (.and (rule v3 v0 v1) (accs v0 v2) :: acc v1 (node v3 v2) :: .app certsClaim v2 ::
        theory (Γ := goals :: goal :: certs :: label :: Γ))
      (ders v0) :=
    ExtDerivation.impE (ExtDerivation.allE v0 listClaim) (ExtDerivation.andER premises)
  have ruleAxiom : ExtDerivation Symbol
      (.and (rule v3 v0 v1) (accs v0 v2) :: acc v1 (node v3 v2) :: .app certsClaim v2 ::
        theory (Γ := goals :: goal :: certs :: label :: Γ)) derRule :=
    ExtDerivation.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ mem_theory_derRule)))
  have ruleClosure : ExtDerivation Symbol
      (.and (rule v3 v0 v1) (accs v0 v2) :: acc v1 (node v3 v2) :: .app certsClaim v2 ::
        theory (Γ := goals :: goal :: certs :: label :: Γ))
      (.imp (rule v3 v0 v1) (.imp (ders v0) (der v1))) :=
    ExtDerivation.allE v1 (ExtDerivation.allE v0 (ExtDerivation.allE v3 ruleAxiom))
  exact ExtDerivation.impE (ExtDerivation.impE ruleClosure (ExtDerivation.andEL premises))
    premisesDerivable

/-- Node case of the induction: `∀ l cs. certsClaim cs → certClaim (node l cs)`. -/
theorem node_case :
    ExtDerivation Symbol (theory (Γ := Γ)) (nodeClosed certClaim certsClaim) := by
  refine ExtDerivation.allI (ExtDerivation.allI (ExtDerivation.impI ?_))
  change ExtDerivation Symbol (.app certsClaim v0 :: theory (Γ := certs :: label :: Γ))
    (.app certClaim (node v1 v0))
  refine lam_intro ?_
  change ExtDerivation Symbol (.app certsClaim v0 :: theory (Γ := certs :: label :: Γ))
    (.all (σ := goal) (.imp (acc v0 (node v2 v1)) (der v0)))
  refine ExtDerivation.allI (ExtDerivation.impI ?_)
  exact node_case_body

/-- Base case of the induction: `certsClaim nil`.  The empty-list equation
forces the premise list to be empty, which is derivable. -/
theorem nil_case : ExtDerivation Symbol (theory (Γ := Γ)) (.app certsClaim nil) := by
  refine lam_intro ?_
  change ExtDerivation Symbol (theory (Γ := Γ))
    (.all (σ := goals) (.imp (accs v0 nil) (ders v0)))
  refine ExtDerivation.allI (ExtDerivation.impI ?_)
  change ExtDerivation Symbol (accs v0 nil :: theory (Γ := goals :: Γ)) (ders v0)
  have nilAxiom : ExtDerivation Symbol (accs v0 nil :: theory (Γ := goals :: Γ)) accsNil :=
    ExtDerivation.hyp (List.mem_cons_of_mem _ mem_theory_accsNil)
  have nilEquation : ExtDerivation Symbol (accs v0 nil :: theory (Γ := goals :: Γ))
      (.eq (accs v0 nil) (.eq v0 goalsNil)) :=
    ExtDerivation.allE v0 nilAxiom
  have empty : ExtDerivation Symbol (accs v0 nil :: theory (Γ := goals :: Γ))
      (.eq v0 goalsNil) :=
    ExtDerivation.impE (ExtDerivation.eqPropEL nilEquation) (ExtDerivation.hyp List.mem_cons_self)
  have congruence : ExtDerivation Symbol (accs v0 nil :: theory (Γ := goals :: Γ))
      (.eq (ders v0) (ders goalsNil)) :=
    ExtDerivation.eqAppArg (.const Symbol.ders) empty
  exact ExtDerivation.impE (ExtDerivation.eqPropER congruence)
    (ExtDerivation.hyp (List.mem_cons_of_mem _ mem_theory_dersNil))

/-- Cons case, innermost part.  In the context `gs, g, ps, cs, c`, the
nonempty-list equation instance `ps = goalsCons g gs ∧ acc g c ∧ accs gs cs`
and the two claims for `c` and `cs` derive `ders ps`. -/
theorem cons_case_body :
    ExtDerivation Symbol
      (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3)) ::
        .ex (σ := goals) (.and (.eq v3 (goalsCons v2 v0)) (.and (acc v2 v5) (accs v0 v4))) ::
        accs v2 (cons v4 v3) :: .app certsClaim v3 :: .app certClaim v4 ::
        theory (Γ := goals :: goal :: goals :: certs :: cert :: Γ))
      (ders v2) := by
  have split : ExtDerivation Symbol
      (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3)) ::
        .ex (σ := goals) (.and (.eq v3 (goalsCons v2 v0)) (.and (acc v2 v5) (accs v0 v4))) ::
        accs v2 (cons v4 v3) :: .app certsClaim v3 :: .app certClaim v4 ::
        theory (Γ := goals :: goal :: goals :: certs :: cert :: Γ))
      (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3))) :=
    ExtDerivation.hyp List.mem_cons_self
  have headClaim : ExtDerivation Symbol
      (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3)) ::
        .ex (σ := goals) (.and (.eq v3 (goalsCons v2 v0)) (.and (acc v2 v5) (accs v0 v4))) ::
        accs v2 (cons v4 v3) :: .app certsClaim v3 :: .app certClaim v4 ::
        theory (Γ := goals :: goal :: goals :: certs :: cert :: Γ))
      (.all (σ := goal) (.imp (acc v0 v5) (der v0))) :=
    lam_elim (ExtDerivation.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  have tailClaim : ExtDerivation Symbol
      (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3)) ::
        .ex (σ := goals) (.and (.eq v3 (goalsCons v2 v0)) (.and (acc v2 v5) (accs v0 v4))) ::
        accs v2 (cons v4 v3) :: .app certsClaim v3 :: .app certClaim v4 ::
        theory (Γ := goals :: goal :: goals :: certs :: cert :: Γ))
      (.all (σ := goals) (.imp (accs v0 v4) (ders v0))) :=
    lam_elim (ExtDerivation.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
  have headDerivable := ExtDerivation.impE (ExtDerivation.allE v1 headClaim)
    (ExtDerivation.andEL (ExtDerivation.andER split))
  have tailDerivable := ExtDerivation.impE (ExtDerivation.allE v0 tailClaim)
    (ExtDerivation.andER (ExtDerivation.andER split))
  have consAxiom : ExtDerivation Symbol
      (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3)) ::
        .ex (σ := goals) (.and (.eq v3 (goalsCons v2 v0)) (.and (acc v2 v5) (accs v0 v4))) ::
        accs v2 (cons v4 v3) :: .app certsClaim v3 :: .app certClaim v4 ::
        theory (Γ := goals :: goal :: goals :: certs :: cert :: Γ)) dersCons :=
    ExtDerivation.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        mem_theory_dersCons)))))
  have consClosure : ExtDerivation Symbol
      (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3)) ::
        .ex (σ := goals) (.and (.eq v3 (goalsCons v2 v0)) (.and (acc v2 v5) (accs v0 v4))) ::
        accs v2 (cons v4 v3) :: .app certsClaim v3 :: .app certClaim v4 ::
        theory (Γ := goals :: goal :: goals :: certs :: cert :: Γ))
      (.imp (der v1) (.imp (ders v0) (ders (goalsCons v1 v0)))) :=
    ExtDerivation.allE v0 (ExtDerivation.allE v1 consAxiom)
  have consDerivable := ExtDerivation.impE (ExtDerivation.impE consClosure headDerivable)
    tailDerivable
  have congruence := ExtDerivation.eqAppArg (.const Symbol.ders) (ExtDerivation.andEL split)
  exact ExtDerivation.impE (ExtDerivation.eqPropER congruence) consDerivable

/-- Cons case of the induction:
`∀ c cs. certClaim c → certsClaim cs → certsClaim (cons c cs)`. -/
theorem cons_case :
    ExtDerivation Symbol (theory (Γ := Γ)) (consClosed certClaim certsClaim) := by
  refine ExtDerivation.allI (ExtDerivation.allI (ExtDerivation.impI
    (ExtDerivation.impI ?_)))
  change ExtDerivation Symbol
    (.app certsClaim v0 :: .app certClaim v1 :: theory (Γ := certs :: cert :: Γ))
    (.app certsClaim (cons v1 v0))
  refine lam_intro ?_
  change ExtDerivation Symbol
    (.app certsClaim v0 :: .app certClaim v1 :: theory (Γ := certs :: cert :: Γ))
    (.all (σ := goals) (.imp (accs v0 (cons v2 v1)) (ders v0)))
  refine ExtDerivation.allI (ExtDerivation.impI ?_)
  change ExtDerivation Symbol
    (accs v0 (cons v2 v1) :: .app certsClaim v1 :: .app certClaim v2 ::
      theory (Γ := goals :: certs :: cert :: Γ))
    (ders v0)
  have consAxiom : ExtDerivation Symbol
      (accs v0 (cons v2 v1) :: .app certsClaim v1 :: .app certClaim v2 ::
        theory (Γ := goals :: certs :: cert :: Γ)) accsCons :=
    ExtDerivation.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ mem_theory_accsCons)))
  have consEquation : ExtDerivation Symbol
      (accs v0 (cons v2 v1) :: .app certsClaim v1 :: .app certClaim v2 ::
        theory (Γ := goals :: certs :: cert :: Γ))
      (.eq (accs v0 (cons v2 v1))
        (.ex (σ := goal) (.ex (σ := goals)
          (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3)))))) :=
    ExtDerivation.allE v0 (ExtDerivation.allE v1 (ExtDerivation.allE v2 consAxiom))
  have decomposition := ExtDerivation.impE (ExtDerivation.eqPropEL consEquation)
    (ExtDerivation.hyp List.mem_cons_self)
  refine ExtDerivation.exE decomposition ?_
  refine ExtDerivation.exE (ExtDerivation.hyp List.mem_cons_self) ?_
  exact cons_case_body

/-- One application of the induction axiom, to the two claims. -/
theorem certClaim_all :
    ExtDerivation Symbol (theory (Γ := Γ)) (.all (σ := cert) (.app certClaim v0)) := by
  have principle : ExtDerivation Symbol (theory (Γ := Γ)) certInduction :=
    ExtDerivation.hyp mem_theory_certInduction
  have atClaims : ExtDerivation Symbol (theory (Γ := Γ))
      (.imp (nodeClosed certClaim certsClaim)
        (.imp (.app certsClaim nil)
          (.imp (consClosed certClaim certsClaim) (.all (σ := cert) (.app certClaim v0))))) :=
    ExtDerivation.allE certsClaim (ExtDerivation.allE certClaim principle)
  exact ExtDerivation.impE (ExtDerivation.impE (ExtDerivation.impE atClaims node_case) nil_case)
    cons_case

/-- **Soundness of replay, derived in the object logic.**  The seven axioms
derive `∀ c g. acc g c → der g`. -/
theorem soundness_derivation : ExtDerivation Symbol (theory (Γ := Γ)) soundness := by
  refine ExtDerivation.allI ?_
  change ExtDerivation Symbol (theory (Γ := cert :: Γ))
    (.all (σ := goal) (.imp (acc v0 v1) (der v0)))
  exact lam_elim (ExtDerivation.allE v0 (certClaim_all (Γ := cert :: Γ)))

/-- **The derivation is intuitionistic.**  Soundness of replay is a
consequence of the seven axioms in every substitutional Kripke–Henkin
structure. -/
theorem soundness_kripkeConsequence :
    KripkeHenkin.Consequence.{0, 0, w} {φ | φ ∈ theory (Γ := [])} soundness :=
  KripkeHenkin.consequence_of_provable ⟨theory, fun _ member => member, soundness_derivation⟩

/-! ## A junk model: the six clauses with a cyclic certificate

Goals and labels have one element each.  Certificates are Booleans: `true` is
the cyclic certificate, the node of the one label whose only child is
`true` itself, and `false` is every other certificate.  The one label
concludes the one goal from the one-goal premise list.  Acceptance holds
exactly of the cycle, and nothing is derivable. -/

namespace JunkModel

abbrev Lifted (α : Type) := ULift.{1, 0} α

/-- Carriers of the junk model. -/
def carrier : BaseSort → Type 1
  | .goal => Lifted Unit
  | .label => Lifted Unit
  | .cert => Lifted Bool
  | .certs => Lifted (List Bool)
  | .goals => Lifted (List Unit)

/-- Acceptance of a child list against a premise list: equal lengths and every
child is the cycle. -/
def acceptsAll : List Unit → List Bool → Prop
  | [], [] => True
  | _ :: premises, child :: children => child = true ∧ acceptsAll premises children
  | _, _ => False

/-- Interpretation of the constants. -/
def constant : {τ : Ty BaseSort} → Symbol τ → Ty.denote.{0, 0} carrier τ
  | _, .node => fun _ children => ⟨decide (children.down = [true])⟩
  | _, .nil => ⟨[]⟩
  | _, .cons => fun child children => ⟨child.down :: children.down⟩
  | _, .goalsNil => ⟨[]⟩
  | _, .goalsCons => fun premise premises => ⟨premise.down :: premises.down⟩
  | _, .rule => fun _ premises _ => ⟨premises.down = [()]⟩
  | _, .acc => fun _ certificate => ⟨certificate.down = true⟩
  | _, .accs => fun premises children => ⟨acceptsAll premises.down children.down⟩
  | _, .der => fun _ => ⟨False⟩
  | _, .ders => fun premises => ⟨premises.down = []⟩

/-- The junk model, with full predicate domains. -/
def model : HenkinModel.{0, 0, 0} BaseSort Symbol :=
  HenkinModel.standard carrier constant

/-- The cyclic certificate is the node of the one label whose only child is
itself. -/
theorem cycle : constant Symbol.node ⟨()⟩ ⟨[true]⟩ = (⟨true⟩ : Lifted Bool) := rfl

theorem acceptsAll_single (children : List Bool) :
    acceptsAll [()] children ↔ children = [true] := by
  rcases children with _ | ⟨child, _ | ⟨next, rest⟩⟩
  · exact ⟨fun h => False.elim h, fun h => nomatch h⟩
  · constructor
    · rintro ⟨rfl, -⟩
      rfl
    · intro h
      cases h
      exact ⟨rfl, trivial⟩
  · constructor
    · rintro ⟨-, h⟩
      exact False.elim h
    · intro h
      cases h

theorem accNode_valid : model.models accNode := by
  intro l _ children _ g _
  change ((decide (children.down = [true])) = true) ↔
    ∃ premises : Lifted (List Unit), True ∧
      (premises.down = [()] ∧ acceptsAll premises.down children.down)
  constructor
  · intro accepted
    exact ⟨⟨[()]⟩, trivial, rfl, (acceptsAll_single _).mpr (of_decide_eq_true accepted)⟩
  · rintro ⟨⟨premises⟩, -, hpremises, haccepts⟩
    change premises = [()] at hpremises
    subst hpremises
    exact decide_eq_true ((acceptsAll_single _).mp haccepts)

theorem accsNil_valid : model.models accsNil := by
  intro premises _
  change acceptsAll premises.down [] ↔ premises = ⟨[]⟩
  rcases premises with ⟨_ | ⟨premise, rest⟩⟩
  · exact ⟨fun _ => rfl, fun _ => trivial⟩
  · exact ⟨fun h => False.elim h, fun h => by cases h⟩

theorem accsCons_valid : model.models accsCons := by
  intro child _ children _ premises _
  change acceptsAll premises.down (child.down :: children.down) ↔
    ∃ g : Lifted Unit, True ∧ ∃ gs : Lifted (List Unit), True ∧
      (premises = ⟨g.down :: gs.down⟩ ∧ child.down = true ∧ acceptsAll gs.down children.down)
  rcases premises with ⟨_ | ⟨premise, rest⟩⟩
  · constructor
    · intro h
      exact False.elim h
    · rintro ⟨g, -, gs, -, h, -⟩
      exact nomatch (congrArg ULift.down h : ([] : List Unit) = g.down :: gs.down)
  · constructor
    · rintro ⟨hchild, hrest⟩
      exact ⟨⟨premise⟩, trivial, ⟨rest⟩, trivial, rfl, hchild, hrest⟩
    · rintro ⟨g, -, gs, -, h, hchild, hrest⟩
      have hrest' : rest = gs.down := (List.cons.inj (congrArg ULift.down h)).2
      rw [hrest']
      exact ⟨hchild, hrest⟩

theorem derRule_valid : model.models derRule := by
  intro _ _ premises _ _ _ hrule hders
  change premises.down = [()] at hrule
  change premises.down = [] at hders
  rw [hrule] at hders
  exact nomatch hders

theorem dersNil_valid : model.models dersNil := by
  change ([] : List Unit) = []
  rfl

theorem dersCons_valid : model.models dersCons := by
  intro _ _ _ _ derivable
  exact False.elim derivable

theorem clauses_valid : ∀ φ ∈ clauses (Γ := []), model.models φ := by
  intro φ membership
  simp only [clauses, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
  · exact accNode_valid
  · exact accsNil_valid
  · exact accsCons_valid
  · exact derRule_valid
  · exact dersNil_valid
  · exact dersCons_valid

/-- The predicate "is not the cycle" is closed under nodes and conses but
excludes the cycle, so induction fails. -/
theorem certInduction_invalid : ¬ model.models certInduction := by
  intro h
  have allNotCycle := h (fun certificate => ⟨certificate.down = false⟩) trivial
    (fun children => ⟨∀ child ∈ children.down, child = false⟩) trivial
    (by
      intro _ _ children _ hchildren
      change decide (children.down = [true]) = false
      apply decide_eq_false
      intro hcycle
      have hmem : true ∈ children.down := by rw [hcycle]; exact List.mem_cons_self
      exact Bool.noConfusion (hchildren true hmem))
    (by
      intro child hchild
      exact nomatch hchild)
    (by
      intro child _ children _ hchild hchildren member hmember
      rcases List.mem_cons.mp hmember with rfl | hmember
      · exact hchild
      · exact hchildren member hmember)
  exact Bool.noConfusion (allNotCycle ⟨true⟩ trivial)

/-- The cycle is accepted for the one goal, which is not derivable. -/
theorem soundness_invalid : ¬ model.models soundness := by
  intro h
  exact h ⟨true⟩ trivial ⟨()⟩ trivial rfl

end JunkModel

/-- Satisfaction of a closed sentence does not depend on how the empty
valuation is presented. -/
theorem models_eq_denote (M : HenkinModel.{0, 0, w} BaseSort Symbol) (φ : Sentence [])
    (ρ : HenkinModel.Valuation M []) : M.models φ = (M.denote φ ρ).down := by
  unfold HenkinModel.models PreModel.models
  apply congrArg ULift.down
  apply congrArg (PreModel.denote M.toPreModel φ)
  funext τ v
  nomatch v

/-- Object derivations from closed hypotheses are valid in every Henkin model
of the hypotheses whose functions respect extensional equality. -/
theorem models_of_derivation (M : HenkinModel.{0, 0, w} BaseSort Symbol)
    (extensional : M.FunctionsRespectEqv) {Δ : List (Sentence [])} {φ : Sentence []}
    (proof : ExtDerivation Symbol Δ φ) (hypotheses : ∀ ψ ∈ Δ, M.models ψ) :
    M.models φ :=
  Eq.mpr (models_eq_denote M φ (fun {_} v => nomatch v))
    (Soundness.extDerivation_sound proof (M := M) (ρ := fun {_} v => nomatch v) extensional
      (by intro τ v; nomatch v)
      (by
        intro ψ membership
        exact Eq.mp (models_eq_denote M ψ _) (hypotheses ψ membership)))

/-- **The induction axiom is needed.**  The six recursion and closure clauses
do not derive soundness: an object derivation would be valid in the junk
model, which validates the clauses and refutes soundness. -/
theorem clauses_do_not_derive_soundness :
    ¬ ExtDerivation Symbol (clauses (Γ := [])) soundness := fun proof =>
  JunkModel.soundness_invalid
    (models_of_derivation JunkModel.model
      (HenkinModel.functionsRespectEqv_of_fullDomains JunkModel.model
        (HenkinModel.fullDomains_standard JunkModel.carrier JunkModel.constant))
      proof JunkModel.clauses_valid)

/-- Soundness holds in every full-domain Henkin model of the seven axioms. -/
theorem models_soundness_of_models_theory
    (M : HenkinModel.{0, 0, w} BaseSort Symbol) (hFull : M.FullDomains)
    (hTheory : ∀ φ ∈ theory (Γ := []), M.models φ) :
    M.models soundness :=
  models_of_derivation M (M.functionsRespectEqv_of_fullDomains hFull)
    soundness_derivation hTheory

end Mettapedia.Logic.HOL.ReplayCore
