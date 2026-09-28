import Mettapedia.OSLF.Syntax.RuleAlgebraInterpretationCoherence
import Mettapedia.OSLF.Syntax.FreeBindingEquationModel
import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Lambda rule constructors over semantic binding-clone models

The Chapter 7 lambda rules can be interpreted over any binding clone, not
only over the free raw-term carrier. Their root and premise endpoints use
the interpreted application, abstraction and semantic substitution. A
binding-clone morphism preserves those endpoints. This is the syntax-model
part of transporting the rule polynomial into a presented equation model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaSemanticRulePolynomial

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingCloneAlgebra
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.TypeTheory

universe u v w

variable {A : BindingCloneAlgebra.Algebra.{u} sig}
variable {B : BindingCloneAlgebra.Algebra.{v} sig}

abbrev SemTerm (A : BindingCloneAlgebra.Algebra.{u} sig)
    (Γ : Ctx sig) := A.substitution.Carrier Γ .term

/-- Semantic application uses the authored binary operator. -/
def app (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (f x : SemTerm A Γ) : SemTerm A Γ :=
  A.operation .app (.cons f (.cons x .nil))

/-- Semantic abstraction consumes a body in the binder-extended context. -/
def lam (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (body : SemTerm A (.term :: Γ)) : SemTerm A Γ :=
  A.operation .lam (.cons body .nil)

/-- The semantic environment replacing the newest binder. -/
def newestEnvironment (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (arg : SemTerm A Γ) :
    Environment sig A.substitution.Carrier (.term :: Γ) Γ
  | _, .zero => arg
  | _, .succ old => A.substitution.injectVar old

/-- Substitute an argument for the newest bound variable and leave all
outer variables as projections. -/
def instantiate (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (body : SemTerm A (.term :: Γ))
    (arg : SemTerm A Γ) : SemTerm A Γ :=
  A.substitution.substitute (newestEnvironment A arg) body

variable (h : FreeBindingClone.Hom A B)

/-- Binding-clone maps preserve semantic application. -/
theorem map_app {Γ : Ctx sig} (f x : SemTerm A Γ) :
    h.raw.map (app A f x) =
      app B (h.raw.map f) (h.raw.map x) := by
  exact h.raw.map_operation .app (.cons f (.cons x .nil))

/-- Binding-clone maps preserve semantic abstraction, including the body
in its extended context. -/
theorem map_lam {Γ : Ctx sig} (body : SemTerm A (.term :: Γ)) :
    h.raw.map (lam A body) = lam B (h.raw.map body) := by
  exact h.raw.map_operation .lam (.cons body .nil)

/-- Full substitution preservation gives the beta-target comparison.
No source-specific first-occurrence depth is inferred. -/
theorem map_instantiate {Γ : Ctx sig}
    (body : SemTerm A (.term :: Γ)) (arg : SemTerm A Γ) :
    h.raw.map (instantiate A body arg) =
      instantiate B (h.raw.map body) (h.raw.map arg) := by
  have envEq :
      (fun s v => h.raw.map (newestEnvironment A arg s v)) =
        newestEnvironment B (h.raw.map arg) := by
    funext s v
    cases v with
    | zero => rfl
    | succ old => exact h.raw.map_variable old
  change h.raw.map
      (A.substitution.substitute (newestEnvironment A arg) body) =
    B.substitution.substitute
      (newestEnvironment B (h.raw.map arg)) (h.raw.map body)
  exact (h.map_substitute (newestEnvironment A arg) body).trans
    (congrArg (fun env => B.substitution.substitute env (h.raw.map body)) envEq)

/-- Semantic reduction judgments retain the full typed context and both
endpoints in that context. -/
abbrev Judgment (A : BindingCloneAlgebra.Algebra.{u} sig) :=
  Σ Γ : Ctx sig, SemTerm A Γ × SemTerm A Γ

def judgment (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (source target : SemTerm A Γ) : Judgment A :=
  ⟨Γ, source, target⟩

/-- The Chapter 7 rules interpreted in a binding-clone model. Beta uses
semantic instantiation; LamCong invokes a premise under one fresh binder. -/
inductive RuleShape (A : BindingCloneAlgebra.Algebra.{u} sig) :
    Judgment A → Type (max u 1) where
  | beta {Γ : Ctx sig} (body : SemTerm A (.term :: Γ))
      (arg : SemTerm A Γ) :
      RuleShape A (judgment A (app A (lam A body) arg)
        (instantiate A body arg))
  | appCongL {Γ : Ctx sig} (source target arg : SemTerm A Γ) :
      RuleShape A (judgment A (app A source arg) (app A target arg))
  | appCongR {Γ : Ctx sig} (funTerm source target : SemTerm A Γ) :
      RuleShape A (judgment A (app A funTerm source) (app A funTerm target))
  | lamCong {Γ : Ctx sig}
      (source target : SemTerm A (.term :: Γ)) :
      RuleShape A (judgment A (lam A source) (lam A target))

/-- Exact recursive premise addresses of a semantic rule. -/
def premisePosition : {j : Judgment A} → RuleShape A j → Type
  | _, .beta _ _ => Empty
  | _, .appCongL _ _ _ => Unit
  | _, .appCongR _ _ _ => Unit
  | _, .lamCong _ _ => Unit

/-- Congruence premises retain their own contexts; LamCong's premise is
indexed by the context extended with the bound variable. -/
def premiseJudgment : {j : Judgment A} →
    (shape : RuleShape A j) → premisePosition shape → Judgment A
  | _, .beta _ _, impossible => impossible.elim
  | _, .appCongL source target _, _ => judgment A source target
  | _, .appCongR _ source target, _ => judgment A source target
  | _, .lamCong source target, _ => judgment A source target

/-- The same rule scheme is meaningful over every semantic binding clone. -/
def rules (A : BindingCloneAlgebra.Algebra.{u} sig) :
    IndexedPolynomial Unit (fun _ => Judgment A) where
  Shape _ j := RuleShape A j
  Position shape := premisePosition shape
  next shape position := premiseJudgment shape position

/-- Each semantic binding clone has a free proof-relevant lambda rule model.
The clone itself is fixed in this fibre; the theorem does not yet assert
initiality of a category combining varying clones and rule models. -/
noncomputable def semanticRuleModelInitial
    (A : BindingCloneAlgebra.Algebra.{u} sig) :
    _root_.CategoryTheory.Limits.IsInitial
      (OperationalRuleModels.free (rules A)) :=
  OperationalRuleModels.freeIsInitial (rules A)

/-- A binding-clone morphism maps both endpoints of a semantic judgment. -/
def mapJudgment (h : FreeBindingClone.Hom A B) :
    Judgment A → Judgment B
  | ⟨Γ, source, target⟩ =>
      ⟨Γ, h.raw.map source, h.raw.map target⟩

/-- Identity clone maps leave both endpoints and their context unchanged. -/
theorem mapJudgment_id (A : BindingCloneAlgebra.Algebra.{u} sig)
    (j : Judgment A) :
    mapJudgment (FreeBindingClone.Hom.id A) j = j := by
  cases j
  rfl

/-- Endpoint interpretation respects composition of binding-clone maps. -/
theorem mapJudgment_comp
    {C : BindingCloneAlgebra.Algebra.{w} sig}
    (f : FreeBindingClone.Hom A B)
    (g : FreeBindingClone.Hom B C) (j : Judgment A) :
    mapJudgment (FreeBindingClone.Hom.comp f g) j =
      mapJudgment g (mapJudgment f j) := by
  cases j
  rfl

/-- Every semantic rule constructor survives a binding-clone morphism,
including beta's substituted target. -/
noncomputable def mapShape (h : FreeBindingClone.Hom A B) :
    {j : Judgment A} → RuleShape A j →
      RuleShape B (mapJudgment h j)
  | _, .beta body arg => by
      change RuleShape B
        (judgment B
          (h.raw.map (app A (lam A body) arg))
          (h.raw.map (instantiate A body arg)))
      rw [map_app h, map_lam h, map_instantiate h]
      exact .beta (h.raw.map body) (h.raw.map arg)
  | _, .appCongL source target arg => by
      change RuleShape B
        (judgment B
          (h.raw.map (app A source arg))
          (h.raw.map (app A target arg)))
      rw [map_app h, map_app h]
      exact .appCongL (h.raw.map source) (h.raw.map target)
        (h.raw.map arg)
  | _, .appCongR funTerm source target => by
      change RuleShape B
        (judgment B
          (h.raw.map (app A funTerm source))
          (h.raw.map (app A funTerm target)))
      rw [map_app h, map_app h]
      exact .appCongR (h.raw.map funTerm) (h.raw.map source)
        (h.raw.map target)
  | _, .lamCong source target => by
      change RuleShape B
        (judgment B
          (h.raw.map (lam A source))
          (h.raw.map (lam A target)))
      rw [map_lam h, map_lam h]
      exact .lamCong (h.raw.map source) (h.raw.map target)

/-- Interpret one authored rule constructor after its recursive premises
have already been interpreted. LamCong's input remains at the extended
binder context. -/
noncomputable def mapTreeLayer (h : FreeBindingClone.Hom A B) :
    {j : Judgment A} → (shape : RuleShape A j) →
      ((p : premisePosition shape) →
        (rules B).Fix () (mapJudgment h (premiseJudgment shape p))) →
      (rules B).Fix () (mapJudgment h j)
  | _, .beta body arg, _children => by
      change (rules B).Fix ()
        (judgment B (h.raw.map (app A (lam A body) arg))
          (h.raw.map (instantiate A body arg)))
      rw [map_app h, map_lam h, map_instantiate h]
      exact .roll (.beta (h.raw.map body) (h.raw.map arg))
        (fun impossible => impossible.elim)
  | _, .appCongL source target arg, children => by
      change (rules B).Fix ()
        (judgment B (h.raw.map (app A source arg))
          (h.raw.map (app A target arg)))
      rw [map_app h, map_app h]
      exact .roll
        (.appCongL (h.raw.map source) (h.raw.map target) (h.raw.map arg))
        (fun _ => children ())
  | _, .appCongR funTerm source target, children => by
      change (rules B).Fix ()
        (judgment B (h.raw.map (app A funTerm source))
          (h.raw.map (app A funTerm target)))
      rw [map_app h, map_app h]
      exact .roll
        (.appCongR (h.raw.map funTerm) (h.raw.map source)
          (h.raw.map target)) (fun _ => children ())
  | _, .lamCong source target, children => by
      change (rules B).Fix ()
        (judgment B (h.raw.map (lam A source))
          (h.raw.map (lam A target)))
      rw [map_lam h, map_lam h]
      exact .roll (.lamCong (h.raw.map source) (h.raw.map target))
        (fun _ => children ())

/-- Interpret every recursive firing tree along a binding-clone morphism.
The recursive child of LamCong remains in its binder-extended context. -/
noncomputable def mapTree (h : FreeBindingClone.Hom A B) :
    (j : Judgment A) → (rules A).Fix () j →
      (rules B).Fix () (mapJudgment h j) :=
  IndexedPolynomial.Fix.eliminate (rules A)
    (fun _ j _ => (rules B).Fix () (mapJudgment h j))
    (fun _ _ shape _children ih => mapTreeLayer h shape ih) ()

/-- The endpoint reduction predicate induced by a proof-relevant semantic
rule model. Different derivations may inhabit the same predicate. -/
def HasStep (A : BindingCloneAlgebra.Algebra.{u} sig)
    (j : Judgment A) : Prop :=
  Nonempty ((rules A).Fix () j)

/-- Clone interpretations preserve existence of a reduction at the exact
interpreted endpoints. The witness itself is carried by `mapTree`. -/
theorem hasStep_map (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (step : HasStep A j) :
    HasStep B (mapJudgment h j) := by
  obtain ⟨tree⟩ := step
  exact ⟨mapTree h j tree⟩

/-- Endpoint-predicate preservation composes without assuming that the two
proof-relevant tree maps are already proved equal. -/
theorem hasStep_map_comp
    {C : BindingCloneAlgebra.Algebra.{w} sig}
    (f : FreeBindingClone.Hom A B)
    (g : FreeBindingClone.Hom B C)
    {j : Judgment A} (step : HasStep A j) :
    HasStep C (mapJudgment (FreeBindingClone.Hom.comp f g) j) := by
  rw [mapJudgment_comp f g j]
  exact hasStep_map g (hasStep_map f step)

/-- Identity semantic interpretation preserves every proof-relevant rule tree,
including recursive evidence under the lambda binder. -/
theorem mapTree_id (A : BindingCloneAlgebra.Algebra sig)
    (j : Judgment A) (tree : (rules A).Fix () j) :
    mapTree (FreeBindingClone.Hom.id A) j tree = tree := by
  exact IndexedPolynomial.Fix.eliminate (rules A)
    (fun _ j tree =>
      mapTree (FreeBindingClone.Hom.id A) j tree = tree)
    (fun base j shape children ih => by
      cases base
      cases shape with
      | beta body arg =>
          change mapTree (FreeBindingClone.Hom.id A) _
              (IndexedPolynomial.Fix.roll
                (RuleShape.beta body arg) children) =
            IndexedPolynomial.Fix.roll
              (RuleShape.beta body arg) children
          rw [show children =
            (fun impossible => impossible.elim) from by
              funext impossible
              exact impossible.elim]
          rfl
      | appCongL source target arg =>
          change mapTree (FreeBindingClone.Hom.id A) _
              (IndexedPolynomial.Fix.roll
                (RuleShape.appCongL source target arg) children) =
            IndexedPolynomial.Fix.roll
              (RuleShape.appCongL source target arg) children
          have childEq : (fun (_ : Unit) =>
              mapTree (FreeBindingClone.Hom.id A)
                ((rules A).next (RuleShape.appCongL source target arg) ())
                (children ())) = children := by
            funext p
            cases p
            exact ih ()
          calc
            mapTree (FreeBindingClone.Hom.id A) _
                (IndexedPolynomial.Fix.roll
                  (RuleShape.appCongL source target arg) children) =
                IndexedPolynomial.Fix.roll
                  (RuleShape.appCongL source target arg)
                  (fun _ => mapTree (FreeBindingClone.Hom.id A)
                    ((rules A).next (RuleShape.appCongL source target arg) ())
                    (children ())) := rfl
            _ = IndexedPolynomial.Fix.roll
                  (RuleShape.appCongL source target arg) children := congrArg
              (IndexedPolynomial.Fix.roll
                (polynomial := rules A) (base := ())
                (RuleShape.appCongL source target arg)) childEq
      | appCongR funTerm source target =>
          change mapTree (FreeBindingClone.Hom.id A) _
              (IndexedPolynomial.Fix.roll
                (RuleShape.appCongR funTerm source target) children) =
            IndexedPolynomial.Fix.roll
              (RuleShape.appCongR funTerm source target) children
          have childEq : (fun (_ : Unit) =>
              mapTree (FreeBindingClone.Hom.id A)
                ((rules A).next (RuleShape.appCongR funTerm source target) ())
                (children ())) = children := by
            funext p
            cases p
            exact ih ()
          calc
            mapTree (FreeBindingClone.Hom.id A) _
                (IndexedPolynomial.Fix.roll
                  (RuleShape.appCongR funTerm source target) children) =
                IndexedPolynomial.Fix.roll
                  (RuleShape.appCongR funTerm source target)
                  (fun _ => mapTree (FreeBindingClone.Hom.id A)
                    ((rules A).next (RuleShape.appCongR funTerm source target) ())
                    (children ())) := rfl
            _ = IndexedPolynomial.Fix.roll
                  (RuleShape.appCongR funTerm source target) children := congrArg
              (IndexedPolynomial.Fix.roll
                (polynomial := rules A) (base := ())
                (RuleShape.appCongR funTerm source target)) childEq
      | lamCong source target =>
          change mapTree (FreeBindingClone.Hom.id A) _
              (IndexedPolynomial.Fix.roll
                (RuleShape.lamCong source target) children) =
            IndexedPolynomial.Fix.roll
              (RuleShape.lamCong source target) children
          have childEq : (fun (_ : Unit) =>
              mapTree (FreeBindingClone.Hom.id A)
                ((rules A).next (RuleShape.lamCong source target) ())
                (children ())) = children := by
            funext p
            cases p
            exact ih ()
          calc
            mapTree (FreeBindingClone.Hom.id A) _
                (IndexedPolynomial.Fix.roll
                  (RuleShape.lamCong source target) children) =
                IndexedPolynomial.Fix.roll
                  (RuleShape.lamCong source target)
                  (fun _ => mapTree (FreeBindingClone.Hom.id A)
                    ((rules A).next (RuleShape.lamCong source target) ())
                    (children ())) := rfl
            _ = IndexedPolynomial.Fix.roll
                  (RuleShape.lamCong source target) children := congrArg
              (IndexedPolynomial.Fix.roll
                (polynomial := rules A) (base := ())
                (RuleShape.lamCong source target)) childEq) () j tree


/-- The semantic operators specialize to the original authored syntax, so
the general rule scheme is anchored to the concrete Chapter 7 calculus. -/
theorem app_terms {Γ : Ctx sig} (f x : Term sig Γ .term) :
    app (BindingCloneAlgebra.terms sig) f x = appT f x := rfl

theorem lam_terms {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term) :
    lam (BindingCloneAlgebra.terms sig) body = lamT body := rfl

theorem instantiate_terms {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (arg : Term sig Γ .term) :
    instantiate (BindingCloneAlgebra.terms sig) body arg = inst body arg := by
  have envEq :
      newestEnvironment (BindingCloneAlgebra.terms sig) arg =
        extend arg := by
    funext s v
    cases v <;> rfl
  exact congrArg (fun env : Sub sig (.term :: Γ) Γ => bind env body) envEq

/-- Embed the existing authored derivation tree into the semantic rule
polynomial over the free binding clone. This is the comparison between the
two representations of the same lambda rules. -/
noncomputable def rawTreeToSemantic :
    (j : LambdaRuleDerivationPolynomial.Judgment) →
      (LambdaRuleDerivationPolynomial.rules).Fix () j →
        (rules (BindingCloneAlgebra.terms sig)).Fix () j :=
  IndexedPolynomial.Fix.eliminate
    LambdaRuleDerivationPolynomial.rules
    (fun _ j _ => (rules (BindingCloneAlgebra.terms sig)).Fix () j)
    (fun _ j shape _children ih => by
      cases shape with
      | beta body arg =>
          change (rules (BindingCloneAlgebra.terms sig)).Fix ()
            (judgment (BindingCloneAlgebra.terms sig)
              (appT (lamT body) arg) (inst body arg))
          rw [← app_terms, ← lam_terms, ← instantiate_terms]
          exact .roll (.beta (A := BindingCloneAlgebra.terms sig) body arg)
            (fun impossible => impossible.elim)
      | appCongL source target arg =>
          change (rules (BindingCloneAlgebra.terms sig)).Fix ()
            (judgment (BindingCloneAlgebra.terms sig)
              (appT source arg) (appT target arg))
          rw [← app_terms, ← app_terms]
          exact .roll (.appCongL (A := BindingCloneAlgebra.terms sig)
            source target arg)
            (fun _ => ih ())
      | appCongR funTerm source target =>
          change (rules (BindingCloneAlgebra.terms sig)).Fix ()
            (judgment (BindingCloneAlgebra.terms sig)
              (appT funTerm source) (appT funTerm target))
          rw [← app_terms, ← app_terms]
          exact .roll (.appCongR (A := BindingCloneAlgebra.terms sig)
            funTerm source target)
            (fun _ => ih ())
      | lamCong source target =>
          change (rules (BindingCloneAlgebra.terms sig)).Fix ()
            (judgment (BindingCloneAlgebra.terms sig)
              (lamT source) (lamT target))
          rw [← lam_terms, ← lam_terms]
          exact .roll (.lamCong (A := BindingCloneAlgebra.terms sig)
            source target)
            (fun _ => ih ())) ()

/-- Reading a semantic rule tree over the free clone recovers the authored
least contextual reduction relation. This is the converse to the preceding
source-to-semantic construction at the unquotiented syntax model. -/
theorem semanticTreeToStep :
    (j : Judgment (BindingCloneAlgebra.terms sig)) →
      (rules (BindingCloneAlgebra.terms sig)).Fix () j →
        LambdaContextualRung.Step j.1 j.2.1 j.2.2 :=
  IndexedPolynomial.Fix.eliminate
    (rules (BindingCloneAlgebra.terms sig))
    (fun _ j _ => LambdaContextualRung.Step j.1 j.2.1 j.2.2)
    (fun _ j shape _children ih => by
      cases shape with
      | beta body arg =>
          change LambdaContextualRung.Step _
            (appT (lamT body) arg)
            (instantiate (BindingCloneAlgebra.terms sig) body arg)
          exact (instantiate_terms body arg).symm ▸
            LambdaContextualRung.Step.beta body arg
      | appCongL source target arg =>
          change LambdaContextualRung.Step _
            (appT source arg) (appT target arg)
          exact .appCongL arg (ih ())
      | appCongR funTerm source target =>
          change LambdaContextualRung.Step _
            (appT funTerm source) (appT funTerm target)
          exact .appCongR funTerm (ih ())
      | lamCong source target =>
          change LambdaContextualRung.Step _
            (lamT source) (lamT target)
          exact .lamCong (ih ())) ()

/-- At the free syntax model, proof-relevant semantic trees have exactly
the judgments of the source's four-rule least relation. -/
theorem sourceStep_iff_semanticTree
    {Γ : Ctx sig} {source target : Term sig Γ .term} :
    LambdaContextualRung.Step Γ source target ↔
      Nonempty
        ((rules (BindingCloneAlgebra.terms sig)).Fix ()
          (judgment (BindingCloneAlgebra.terms sig) source target)) := by
  constructor
  · intro step
    obtain ⟨tree⟩ := LambdaRuleDerivationPolynomial.ofStep_nonempty step
    exact ⟨rawTreeToSemantic
      (LambdaRuleDerivationPolynomial.judgment source target) tree⟩
  · rintro ⟨tree⟩
    exact semanticTreeToStep _ tree

/-- A variable is not the source of any rule tree in the actual free lambda
syntax. This fails if a semantic equation later identifies that variable
with a reducible composite; no unrestricted quotient reflection is claimed. -/
theorem variable_has_no_semantic_tree {Γ : Ctx sig}
    (v : Var Γ .term) {target : Term sig Γ .term} :
    ¬ Nonempty
      ((rules (BindingCloneAlgebra.terms sig)).Fix ()
        (judgment (BindingCloneAlgebra.terms sig) (.var v) target)) := by
  intro inhabited
  exact LambdaContextualRung.variable_has_no_step v
    (sourceStep_iff_semanticTree.mpr inhabited)

/-- Interpret an authored lambda derivation in the presented equation
model. Its states become equation classes while its proof-relevant rule
constructor tree is transported through the quotient clone morphism. -/
noncomputable def presentedTree
    {M : List (MetaArity sig)} (E : List (EqAxiom sig M))
    (j : LambdaRuleDerivationPolynomial.Judgment)
    (tree : (LambdaRuleDerivationPolynomial.rules).Fix () j) :
    (rules (BindingEquationQuotientModel.algebra E)).Fix ()
      (mapJudgment (BindingEquationQuotientModel.projection E) j) :=
  mapTree (BindingEquationQuotientModel.projection E) j
    (rawTreeToSemantic j tree)

/-- The actual authored equation quotient also has an initial rule-model
fibre, with states already interpreted as equation classes. -/
noncomputable def presentedRuleModelInitial
    {M : List (MetaArity sig)} (E : List (EqAxiom sig M)) :
    _root_.CategoryTheory.Limits.IsInitial
      (OperationalRuleModels.free
        (rules (BindingEquationQuotientModel.algebra E))) :=
  semanticRuleModelInitial (BindingEquationQuotientModel.algebra E)

/-- Every authored lambda step has a proof-relevant realization in any
semantic binding clone, under the unique interpretation of raw syntax.
The target is the actual interpreted reduct, including beta substitution. -/
theorem sourceStep_to_model
    (B : BindingCloneAlgebra.Algebra.{v} sig)
    (h : FreeBindingClone.Hom (BindingCloneAlgebra.terms sig) B)
    {Γ : Ctx sig} {source target : Term sig Γ .term}
    (step : LambdaContextualRung.Step Γ source target) :
    Nonempty
      ((rules B).Fix ()
        (judgment B (h.raw.map source) (h.raw.map target))) := by
  obtain ⟨tree⟩ := LambdaRuleDerivationPolynomial.ofStep_nonempty step
  exact ⟨mapTree h
    (LambdaRuleDerivationPolynomial.judgment source target)
    (rawTreeToSemantic
      (LambdaRuleDerivationPolynomial.judgment source target) tree)⟩

/-- Every checked source step gives a retained firing derivation at the
exact two equation-class endpoints of the presented model. This implication
does not identify different source derivations or assume converse reflection
after equations have identified states. -/
theorem sourceStep_to_presented
    {M : List (MetaArity sig)} (E : List (EqAxiom sig M))
    {Γ : Ctx sig} {source target : Term sig Γ .term}
    (step : LambdaContextualRung.Step Γ source target) :
    Nonempty
      ((rules (BindingEquationQuotientModel.algebra E)).Fix ()
        (judgment (BindingEquationQuotientModel.algebra E)
          (Quotient.mk _ source) (Quotient.mk _ target))) := by
  obtain ⟨tree⟩ := LambdaRuleDerivationPolynomial.ofStep_nonempty step
  exact ⟨presentedTree E
    (LambdaRuleDerivationPolynomial.judgment source target) tree⟩

#print axioms map_instantiate
#print axioms semanticRuleModelInitial
#print axioms mapTree
#print axioms mapTree_id
#print axioms hasStep_map_comp
#print axioms rawTreeToSemantic
#print axioms sourceStep_iff_semanticTree
#print axioms variable_has_no_semantic_tree
#print axioms sourceStep_to_model
#print axioms sourceStep_to_presented
#print axioms presentedRuleModelInitial

end Mettapedia.OSLF.Binding.LambdaSemanticRulePolynomial
