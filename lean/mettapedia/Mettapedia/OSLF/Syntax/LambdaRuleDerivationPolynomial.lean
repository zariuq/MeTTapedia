import Mettapedia.OSLF.Syntax.LambdaContextualRung
import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Indexed derivation trees for the Chapter 7 lambda rules

Each constructor is one of the four contextual lambda rules. Its index
contains the ambient binding context and both endpoints. A congruence rule
has one recursive premise; abstraction congruence changes the premise index
to the context extended by the binder. The indexed polynomial's fixed point
retains constructor identity and a tree of premise evidence.

The existing source relation is proposition-valued. It is equivalent to
inhabitedness of this proof-relevant family, rather than to equality of proof
objects. This is the exact boundary needed before rule histories and folds
are compared with general authored operational semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.LambdaContextualRung

/-- A contextual reduction judgment, including its actual raw source and
target terms rather than only their equation classes. -/
abbrev Judgment := Σ Γ : Ctx sig,
  Term sig Γ .term × Term sig Γ .term

def judgment {Γ : Ctx sig} (source target : Term sig Γ .term) : Judgment :=
  ⟨Γ, source, target⟩

/-- The four displayed Chapter 7 rules as constructor shapes. -/
inductive RuleShape : Judgment → Type where
  | beta {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term)
      (arg : Term sig Γ .term) :
      RuleShape (judgment (appT (lamT body) arg) (inst body arg))
  | appCongL {Γ : Ctx sig} (source target arg : Term sig Γ .term) :
      RuleShape (judgment (appT source arg) (appT target arg))
  | appCongR {Γ : Ctx sig} (funTerm source target : Term sig Γ .term) :
      RuleShape (judgment (appT funTerm source) (appT funTerm target))
  | lamCong {Γ : Ctx sig}
      (source target : Term sig (.term :: Γ) .term) :
      RuleShape (judgment (lamT source) (lamT target))

/-- An exact premise address of a rule constructor. Root beta has none;
each congruence rule has one. -/
def premisePosition : {j : Judgment} → RuleShape j → Type
  | _, .beta _ _ => Empty
  | _, .appCongL _ _ _ => Unit
  | _, .appCongR _ _ _ => Unit
  | _, .lamCong _ _ => Unit

/-- The judgment required at each premise address. In particular, the body
premise of LamCong lives in the extended binder context. -/
def premiseJudgment : {j : Judgment} →
    (shape : RuleShape j) → premisePosition shape → Judgment
  | _, .beta _ _, impossible => impossible.elim
  | _, .appCongL source target _, _ => judgment source target
  | _, .appCongR _ source target, _ => judgment source target
  | _, .lamCong source target, _ => judgment source target

/-- The actual Chapter 7 rule format as a strictly positive indexed
polynomial. Its base is fixed, while the full context travels in the index
so binder-local premises can change context. -/
def rules : IndexedPolynomial Unit (fun _ => Judgment) where
  Shape _ j := RuleShape j
  Position shape := premisePosition shape
  next shape position := premiseJudgment shape position

abbrev Derivation {Γ : Ctx sig} (source target : Term sig Γ .term) :=
  rules.Fix () (judgment source target)

/-- Each proof-relevant derivation realizes the existing least relation.
The motive is proposition-valued; no equality or uniqueness of proof trees
is assumed. -/
theorem toStep : (j : Judgment) → rules.Fix () j →
    LambdaContextualRung.Step j.1 j.2.1 j.2.2 :=
  IndexedPolynomial.Fix.eliminate rules
    (fun _ j _ => LambdaContextualRung.Step j.1 j.2.1 j.2.2)
    (fun _ j shape _children ih => by
      cases shape with
      | beta body arg => exact LambdaContextualRung.Step.beta body arg
      | appCongL source target arg =>
          exact LambdaContextualRung.Step.appCongL arg (ih ())
      | appCongR funTerm source target =>
          exact LambdaContextualRung.Step.appCongR funTerm (ih ())
      | lamCong source target =>
          exact LambdaContextualRung.Step.lamCong (ih ())) ()

/-- Every proof of the proposition-valued least relation has a derivation
tree. Since the source is a proposition, the conclusion is merely inhabited
and does not pretend to recover a particular source proof object. -/
theorem ofStep_nonempty {Γ : Ctx sig}
    {source target : Term sig Γ .term}
    (h : LambdaContextualRung.Step Γ source target) :
    Nonempty (Derivation source target) := by
  induction h with
  | beta body arg =>
      exact ⟨.roll (.beta body arg) (fun impossible => impossible.elim)⟩
  | appCongL arg h ih =>
      obtain ⟨child⟩ := ih
      exact ⟨.roll (.appCongL _ _ arg) (fun _ => child)⟩
  | appCongR funTerm h ih =>
      obtain ⟨child⟩ := ih
      exact ⟨.roll (.appCongR funTerm _ _) (fun _ => child)⟩
  | lamCong h ih =>
      obtain ⟨child⟩ := ih
      exact ⟨.roll (.lamCong _ _) (fun _ => child)⟩

/-- The proof-relevant constructor-tree semantics and the original four-rule
propositional relation agree on exactly the same open judgments. -/
theorem step_iff_derivation {Γ : Ctx sig}
    {source target : Term sig Γ .term} :
    LambdaContextualRung.Step Γ source target ↔
      Nonempty (Derivation source target) := by
  constructor
  · exact ofStep_nonempty
  · rintro ⟨tree⟩
    exact toStep _ tree

/-- Reindex an entire proof-relevant firing tree by an ambient substitution.
LamCong transports its recursive premise with the lifted substitution in the
binder-extended context. No event is reconstructed from endpoint existence. -/
noncomputable def substituteTree :
    (j : Judgment) → rules.Fix () j →
      {Δ : Ctx sig} → (σ : Sub sig j.1 Δ) →
        rules.Fix ()
          (judgment (bind σ j.2.1) (bind σ j.2.2)) :=
  IndexedPolynomial.Fix.eliminate rules
    (fun _ j _ => ∀ {Δ : Ctx sig} (σ : Sub sig j.1 Δ),
      rules.Fix () (judgment (bind σ j.2.1) (bind σ j.2.2)))
    (fun _ j shape _children ih => by
      cases shape with
      | @beta Γ body arg =>
          intro Δ σ
          change Sub sig Γ Δ at σ
          have commuting :=
            ContextualLinearSubstitution.bind_inst σ body arg
          change rules.Fix ()
            (judgment (bind σ (appT (lamT body) arg))
              (bind σ (inst body arg)))
          rw [bind_appT, bind_lamT, commuting]
          exact IndexedPolynomial.Fix.roll
            (polynomial := rules) (base := ())
            (RuleShape.beta
              (bind (liftSub σ [Srt.term]) body) (bind σ arg))
            (fun impossible => impossible.elim)
      | @appCongL Γ source target arg =>
          intro Δ σ
          change Sub sig Γ Δ at σ
          change rules.Fix ()
            (judgment (bind σ (appT source arg))
              (bind σ (appT target arg)))
          rw [bind_appT, bind_appT]
          exact IndexedPolynomial.Fix.roll
            (polynomial := rules) (base := ())
            (RuleShape.appCongL
              (bind σ source) (bind σ target) (bind σ arg))
            (fun _ => ih () σ)
      | @appCongR Γ funTerm source target =>
          intro Δ σ
          change Sub sig Γ Δ at σ
          change rules.Fix ()
            (judgment (bind σ (appT funTerm source))
              (bind σ (appT funTerm target)))
          rw [bind_appT, bind_appT]
          exact IndexedPolynomial.Fix.roll
            (polynomial := rules) (base := ())
            (RuleShape.appCongR
              (bind σ funTerm) (bind σ source) (bind σ target))
            (fun _ => ih () σ)
      | @lamCong Γ source target =>
          intro Δ σ
          change Sub sig Γ Δ at σ
          change rules.Fix ()
            (judgment (bind σ (lamT source))
              (bind σ (lamT target)))
          rw [bind_lamT, bind_lamT]
          exact IndexedPolynomial.Fix.roll
            (polynomial := rules) (base := ())
            (RuleShape.lamCong
              (bind (liftSub σ [Srt.term]) source)
              (bind (liftSub σ [Srt.term]) target))
            (fun _ => ih () (liftSub σ [Srt.term]))) ()

/-- The rule names retained in a derivation history. -/
inductive RuleTag where
  | beta | appCongL | appCongR | lamCong
  deriving DecidableEq, Repr

/-- Interpret every rule constructor as its tag followed by the history of
its one premise, when present. This is an actual algebra of the indexed
operational polynomial. -/
def historyAlgebra : rules.Algebra (fun _ _ => List RuleTag) where
  act := by
    intro base index layer
    rcases layer with ⟨shape, children⟩
    change RuleShape index at shape
    cases shape with
    | beta body arg => exact [.beta]
    | appCongL source target arg => exact .appCongL :: children ()
    | appCongR funTerm source target => exact .appCongR :: children ()
    | lamCong source target => exact .lamCong :: children ()

/-- The canonical fold retains the entire ordered rule history. -/
noncomputable def history {j : Judgment} (tree : rules.Fix () j) :
    List RuleTag :=
  IndexedPolynomial.Fix.fold rules historyAlgebra.act () j tree

/-- Every interpretation respecting the four rule constructors agrees with
the canonical history fold on every derivation, including open premises. -/
theorem history_unique
    (candidate : IndexedPolynomial.Algebra.Hom
      (IndexedPolynomial.Algebra.initial rules) historyAlgebra)
    (j : Judgment) (tree : rules.Fix () j) :
    candidate.toFun () j tree = history tree := by
  exact IndexedPolynomial.Algebra.hom_eq_fold
    historyAlgebra candidate () j tree

/-- A beta firing whose argument is the variable bound by an enclosing
lambda. The target is left in its exact intrinsic `inst` form. -/
def openBetaTree : Derivation
    (appT (lamT (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term)))
      (Term.var (Var.zero : Var [Srt.term] Srt.term)))
    (inst (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term))
      (Term.var (Var.zero : Var [Srt.term] Srt.term))) :=
  .roll (.beta _ _) (fun impossible => impossible.elim)

/-- The abstraction congruence constructor consumes the preceding premise
at the extended context, producing a closed outer firing. -/
def closedLamTree : Derivation
    (lamT (appT
      (lamT (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term)))
      (Term.var (Var.zero : Var [Srt.term] Srt.term))))
    (lamT (inst
      (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term))
      (Term.var (Var.zero : Var [Srt.term] Srt.term)))) :=
  .roll (.lamCong _ _) (fun _ => openBetaTree)

theorem open_history : history openBetaTree = [.beta] := rfl

theorem closed_history : history closedLamTree = [.lamCong, .beta] := rfl

/-- The closed constructor tree has exactly the endpoints of the previously
checked open-premise regression. -/
theorem closed_tree_is_source_step :
    LambdaContextualRung.Step []
      (lamT (appT (lamT (.var .zero)) (.var .zero)))
      (lamT (.var .zero)) := by
  have step := toStep _ closedLamTree
  change LambdaContextualRung.Step []
    (lamT (appT (lamT (.var .zero)) (.var .zero)))
    (lamT (inst (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term))
      (Term.var (Var.zero : Var [Srt.term] Srt.term)))) at step
  have hplug :
      inst (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term))
          (Term.var (Var.zero : Var [Srt.term] Srt.term)) =
        (Term.var Var.zero : Term sig [Srt.term] Srt.term) :=
    inst_hole _
  simpa only [hplug] using step

/-- Variables have no derivation tree. This is a negative control for the
constructor correspondence, not a consequence of an empty carrier. -/
theorem variable_has_no_derivation {Γ : Ctx sig} (v : Var Γ .term)
    {target : Term sig Γ .term} :
    ¬ Nonempty (Derivation (.var v) target) := by
  intro inhabited
  exact LambdaContextualRung.variable_has_no_step v
    (step_iff_derivation.mpr inhabited)

#print axioms step_iff_derivation
#print axioms history_unique
#print axioms substituteTree
#print axioms closed_tree_is_source_step
#print axioms variable_has_no_derivation

end Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial
