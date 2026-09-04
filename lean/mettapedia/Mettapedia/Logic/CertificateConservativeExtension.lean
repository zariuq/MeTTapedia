import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mettapedia.Logic.FinitaryRuleSystem.Tree
import Mettapedia.Logic.RuleConservativeExtension

/-!
# Certificate elimination for conservative rule extensions

Logical admissibility alone says that an added rule changes no theorem.  A
replay boundary needs stronger data: an accepted use of the added rule must be
expandable into an accepted certificate over the base rule interface.  This
file defines that data, compiles complete extended certificates, and records a
compositional node budget for the expansion.
-/

set_option autoImplicit false

namespace Mettapedia.Logic

open scoped BigOperators

universe u v w

variable {J : Type u}

/-- A certificate whose replay succeeds and whose conclusion is fixed. -/
structure AcceptedCertificate
    {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (conclusion : J) : Type (max u v) where
  certificate : Derivation J interface.W
  accepted : certificate.valid interface = true
  concludes : certificate.concl = conclusion

namespace AcceptedCertificate

/-- The physical node count of an accepted certificate. -/
def nodeCount {rules : List J → J → Prop}
    {interface : RuleWitness.{u, v} rules} {conclusion : J}
    (certificate : AcceptedCertificate interface conclusion) : Nat :=
  certificate.certificate.nodeCount

/-- Build an accepted parent certificate from an accepted rule witness and
accepted certificates for the listed premises. -/
def node {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {n : Nat}
    (witness : interface.W) (conclusion : J) (premises : Fin n → J)
    (rootAccepted :
      interface.isInstance witness (List.ofFn premises) conclusion = true)
    (children : (i : Fin n) → AcceptedCertificate interface (premises i)) :
    AcceptedCertificate interface conclusion := by
  refine
    { certificate := .node conclusion witness n
        (fun i => (children i).certificate)
      accepted := ?_
      concludes := rfl }
  simp only [Derivation.valid, Bool.and_eq_true, List.all_eq_true,
    List.forall_mem_ofFn_iff, id]
  refine ⟨?_, fun i => (children i).accepted⟩
  have pointwise :
      (fun i : Fin n => (children i).certificate.concl) = premises := by
    funext i
    exact (children i).concludes
  rw [pointwise]
  exact rootAccepted

@[simp] theorem node_nodeCount {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {n : Nat}
    (witness : interface.W) (conclusion : J) (premises : Fin n → J)
    (rootAccepted :
      interface.isInstance witness (List.ofFn premises) conclusion = true)
    (children : (i : Fin n) → AcceptedCertificate interface (premises i)) :
    (node interface witness conclusion premises rootAccepted children).nodeCount =
      1 + ∑ i : Fin n, (children i).nodeCount := rfl

end AcceptedCertificate

namespace RuleWitness

/-- The canonical tagged witness interface for the union of two rule
predicates.  The tag preserves which side licensed each rule application. -/
def sum {rules additional : List J → J → Prop}
    (base : RuleWitness.{u, v} rules)
    (extra : RuleWitness.{u, w} additional) :
    RuleWitness (extendRules rules additional) where
  W := Sum base.W extra.W
  isInstance
    | .inl witness => base.isInstance witness
    | .inr witness => extra.isInstance witness
  sound witness premises conclusion accepted := by
    cases witness with
    | inl witness => exact Or.inl (base.sound witness premises conclusion accepted)
    | inr witness => exact Or.inr (extra.sound witness premises conclusion accepted)
  complete premises conclusion rule := by
    rcases rule with baseRule | extraRule
    · obtain ⟨witness, accepted⟩ := base.complete premises conclusion baseRule
      exact ⟨.inl witness, accepted⟩
    · obtain ⟨witness, accepted⟩ := extra.complete premises conclusion extraRule
      exact ⟨.inr witness, accepted⟩

@[simp] theorem sum_isInstance_inl
    {rules additional : List J → J → Prop}
    (base : RuleWitness.{u, v} rules)
    (extra : RuleWitness.{u, w} additional) (witness : base.W)
    (premises : List J) (conclusion : J) :
    (base.sum extra).isInstance (.inl witness) premises conclusion =
      base.isInstance witness premises conclusion := rfl

@[simp] theorem sum_isInstance_inr
    {rules additional : List J → J → Prop}
    (base : RuleWitness.{u, v} rules)
    (extra : RuleWitness.{u, w} additional) (witness : extra.W)
    (premises : List J) (conclusion : J) :
    (base.sum extra).isInstance (.inr witness) premises conclusion =
      extra.isInstance witness premises conclusion := rfl

end RuleWitness

/-- Constructive evidence that every accepted additional-rule witness can be
expanded into a valid base certificate from valid base certificates for its
premises.  The output certificate and its node bound are returned together,
so the cost receipt cannot drift away from the artifact it measures. -/
structure AdditionalRuleCertificateCompiler
    {rules additional : List J → J → Prop}
    (base : RuleWitness.{u, v} rules)
    (extra : RuleWitness.{u, w} additional) : Type (max u v w) where
  overhead : extra.W → List J → J → Nat
  compileWithBound : ∀ {n : Nat} (witness : extra.W) (conclusion : J)
      (premises : Fin n → J),
      (accepted :
        extra.isInstance witness (List.ofFn premises) conclusion = true) →
      (children :
        (i : Fin n) → AcceptedCertificate base (premises i)) →
      { output : AcceptedCertificate base conclusion //
        output.nodeCount ≤
          overhead witness (List.ofFn premises) conclusion +
            ∑ i : Fin n, (children i).nodeCount }

namespace AdditionalRuleCertificateCompiler

variable {rules additional : List J → J → Prop}
variable {base : RuleWitness.{u, v} rules}
variable {extra : RuleWitness.{u, w} additional}

/-- Forget the local cost receipt after constructing a base certificate. -/
def compile (compiler : AdditionalRuleCertificateCompiler base extra)
    {n : Nat} (witness : extra.W) (conclusion : J)
    (premises : Fin n → J)
    (accepted : extra.isInstance witness (List.ofFn premises) conclusion = true)
    (children : (i : Fin n) → AcceptedCertificate base (premises i)) :
    AcceptedCertificate base conclusion :=
  (compiler.compileWithBound witness conclusion premises accepted children).1

/-- The receipt paired with a local compilation result. -/
theorem compile_nodeCount_le
    (compiler : AdditionalRuleCertificateCompiler base extra)
    {n : Nat} (witness : extra.W) (conclusion : J)
    (premises : Fin n → J)
    (accepted : extra.isInstance witness (List.ofFn premises) conclusion = true)
    (children : (i : Fin n) → AcceptedCertificate base (premises i)) :
    (compiler.compile witness conclusion premises accepted children).nodeCount ≤
      compiler.overhead witness (List.ofFn premises) conclusion +
        ∑ i : Fin n, (children i).nodeCount :=
  (compiler.compileWithBound witness conclusion premises accepted children).2

/-- Budget obtained by replacing every added-rule node with its declared local
overhead and recursively budgeting its children. -/
def compilationBudget
    (compiler : AdditionalRuleCertificateCompiler base extra) :
    Derivation J (base.sum extra).W → Nat
  | .node _conclusion (.inl _) n children =>
      1 + ∑ i : Fin n, compilationBudget compiler (children i)
  | .node conclusion (.inr witness) n children =>
      compiler.overhead witness
          (List.ofFn fun i => (children i).concl) conclusion +
        ∑ i : Fin n, compilationBudget compiler (children i)

/-- Compile a successfully replayed certificate for the tagged rule union into
a successfully replayed certificate for the base interface. -/
def compileAccepted
    (compiler : AdditionalRuleCertificateCompiler base extra) :
    ∀ (source : Derivation J (base.sum extra).W),
      source.valid (base.sum extra) = true →
      AcceptedCertificate base source.concl
  | .node conclusion (.inl witness) n children, accepted => by
      simp only [Derivation.valid, RuleWitness.sum_isInstance_inl,
        Bool.and_eq_true, List.all_eq_true, List.forall_mem_ofFn_iff, id]
        at accepted
      let compiledChild : (i : Fin n) → AcceptedCertificate base (children i).concl :=
        fun i => compileAccepted compiler (children i) (accepted.2 i)
      refine
        { certificate := .node conclusion witness n
            (fun i => (compiledChild i).certificate)
          accepted := ?_
          concludes := rfl }
      simp only [Derivation.valid, Bool.and_eq_true, List.all_eq_true,
        List.forall_mem_ofFn_iff, id]
      refine ⟨?_, fun i => (compiledChild i).accepted⟩
      have pointwise :
          (fun i : Fin n => (compiledChild i).certificate.concl) =
            fun i => (children i).concl := by
        funext i
        exact (compiledChild i).concludes
      rw [pointwise]
      exact accepted.1
  | .node conclusion (.inr witness) n children, accepted => by
      simp only [Derivation.valid, RuleWitness.sum_isInstance_inr,
        Bool.and_eq_true, List.all_eq_true, List.forall_mem_ofFn_iff, id]
        at accepted
      exact compiler.compile witness conclusion (fun i => (children i).concl)
        accepted.1 (fun i =>
          compileAccepted compiler (children i) (accepted.2 i))

/-- The compiled base certificate respects the compositional budget obtained
from the declared overhead of each eliminated added-rule node. -/
theorem compileAccepted_nodeCount_le
    (compiler : AdditionalRuleCertificateCompiler base extra) :
    ∀ (source : Derivation J (base.sum extra).W)
      (accepted : source.valid (base.sum extra) = true),
      (compileAccepted compiler source accepted).nodeCount ≤
        compilationBudget compiler source := by
  intro source
  induction source with
  | node conclusion witness n children ih =>
      intro accepted
      cases witness with
      | inl witness =>
          simp only [Derivation.valid, RuleWitness.sum_isInstance_inl,
            Bool.and_eq_true, List.all_eq_true,
            List.forall_mem_ofFn_iff, id] at accepted
          simp only [compileAccepted, AcceptedCertificate.nodeCount,
            Derivation.nodeCount_node, compilationBudget]
          exact Nat.add_le_add_left
            (Finset.sum_le_sum fun i _ => ih i (accepted.2 i)) 1
      | inr witness =>
          simp only [Derivation.valid, RuleWitness.sum_isInstance_inr,
            Bool.and_eq_true, List.all_eq_true,
            List.forall_mem_ofFn_iff, id] at accepted
          let compiledChild :
              (i : Fin n) → AcceptedCertificate base (children i).concl :=
            fun i => compileAccepted compiler (children i) (accepted.2 i)
          have localBound := compiler.compile_nodeCount_le witness conclusion
            (fun i => (children i).concl) accepted.1 compiledChild
          have childrenBound :
              (∑ i : Fin n, (compiledChild i).nodeCount) ≤
                ∑ i : Fin n, compilationBudget compiler (children i) :=
            Finset.sum_le_sum fun i _ => ih i (accepted.2 i)
          exact localBound.trans
            (Nat.add_le_add_left childrenBound
              (compiler.overhead witness
                (List.ofFn fun i => (children i).concl) conclusion))

/-- Proof-relevant elimination of every accepted extension certificate implies
ordinary conservativity of the rule extension. -/
theorem sameDerivability
    (compiler : AdditionalRuleCertificateCompiler base extra) :
    SameDerivability (extendRules rules additional) rules := by
  intro judgment
  constructor
  · intro derivable
    obtain ⟨source, sourceAccepted, sourceConcludes⟩ :=
      Derives.exists_derivation (base.sum extra) derivable
    let output := compiler.compileAccepted source sourceAccepted
    have result := Derivation.valid_sound base
      output.certificate output.accepted
    rw [output.concludes, sourceConcludes] at result
    exact result
  · exact Derives.mono (fun _premises _conclusion rule => Or.inl rule)

/-- Consequently, every rule instance recognized by the added interface is
logically admissible in the base rule system. -/
theorem additionalRule_admissible
    (compiler : AdditionalRuleCertificateCompiler base extra) :
    ∀ premises conclusion, additional premises conclusion →
      RuleInstanceAdmissible rules premises conclusion :=
  (extendRules_sameDerivability_iff rules additional).mp
    compiler.sameDerivability

end AdditionalRuleCertificateCompiler

namespace ConservativeExtensionCanary

inductive BaseRuleWitness where
  | axiomA
  | aToB
  | bToC
deriving DecidableEq

def baseRuleIsInstance (witness : BaseRuleWitness)
    (premises : List Judgment) (conclusion : Judgment) : Bool :=
  match witness with
  | .axiomA => decide (premises = [] ∧ conclusion = .a)
  | .aToB => decide (premises = [.a] ∧ conclusion = .b)
  | .bToC => decide (premises = [.b] ∧ conclusion = .c)

/-- Exact replay interface for the three base rules used by the conservative
extension canary. -/
def baseRuleInterface : RuleWitness BaseRule where
  W := BaseRuleWitness
  isInstance := baseRuleIsInstance
  sound witness premises conclusion accepted := by
    cases witness with
    | axiomA =>
        simp only [baseRuleIsInstance, decide_eq_true_eq] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact BaseRule.a
    | aToB =>
        simp only [baseRuleIsInstance, decide_eq_true_eq] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact BaseRule.aToB
    | bToC =>
        simp only [baseRuleIsInstance, decide_eq_true_eq] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact BaseRule.bToC
  complete premises conclusion rule := by
    cases rule with
    | a => exact ⟨.axiomA, by decide⟩
    | aToB => exact ⟨.aToB, by decide⟩
    | bToC => exact ⟨.bToC, by decide⟩

inductive ShortcutRuleWitness where
  | aToC
deriving DecidableEq

def shortcutRuleIsInstance (_witness : ShortcutRuleWitness)
    (premises : List Judgment) (conclusion : Judgment) : Bool :=
  decide (premises = [.a] ∧ conclusion = .c)

/-- Exact replay interface for the admissible shortcut `a ⊢ c`. -/
def shortcutRuleInterface : RuleWitness ShortcutRule where
  W := ShortcutRuleWitness
  isInstance := shortcutRuleIsInstance
  sound witness premises conclusion accepted := by
    cases witness
    simp only [shortcutRuleIsInstance, decide_eq_true_eq] at accepted
    rcases accepted with ⟨rfl, rfl⟩
    exact ShortcutRule.aToC
  complete premises conclusion rule := by
    cases rule
    exact ⟨.aToC, by decide⟩

/-- Expand one accepted `a ⊢ c` shortcut into the two base steps
`a ⊢ b ⊢ c`, returning the exact local node count with the certificate. -/
def compileShortcutWithCost {n : Nat} (witness : shortcutRuleInterface.W)
    (conclusion : Judgment) (premises : Fin n → Judgment)
    (accepted : shortcutRuleInterface.isInstance witness
      (List.ofFn premises) conclusion = true)
    (children : (i : Fin n) →
      AcceptedCertificate baseRuleInterface (premises i)) :
    { output : AcceptedCertificate baseRuleInterface conclusion //
      output.nodeCount = 2 + ∑ i : Fin n, (children i).nodeCount } := by
  cases witness
  simp only [shortcutRuleInterface, shortcutRuleIsInstance,
    decide_eq_true_eq] at accepted
  rcases accepted with ⟨premisesEq, conclusionEq⟩
  subst conclusion
  have lengthEq := congrArg List.length premisesEq
  simp only [List.length_ofFn, List.length_singleton] at lengthEq
  subst n
  have premisesFunctionEq : premises = fun _ : Fin 1 => Judgment.a := by
    apply List.ofFn_injective
    simpa using premisesEq
  subst premises
  let bCertificate : AcceptedCertificate baseRuleInterface Judgment.b :=
    AcceptedCertificate.node baseRuleInterface .aToB Judgment.b
      (fun _ : Fin 1 => Judgment.a) (by decide) children
  let cCertificate : AcceptedCertificate baseRuleInterface Judgment.c :=
    AcceptedCertificate.node baseRuleInterface .bToC Judgment.c
      (fun _ : Fin 1 => Judgment.b) (by decide) (fun _ => bCertificate)
  refine ⟨cCertificate, ?_⟩
  simp [cCertificate, bCertificate, AcceptedCertificate.node_nodeCount]
  omega

/-- The certificate component of exact shortcut expansion. -/
def compileShortcut {n : Nat} (witness : shortcutRuleInterface.W)
    (conclusion : Judgment) (premises : Fin n → Judgment)
    (accepted : shortcutRuleInterface.isInstance witness
      (List.ofFn premises) conclusion = true)
    (children : (i : Fin n) →
      AcceptedCertificate baseRuleInterface (premises i)) :
    AcceptedCertificate baseRuleInterface conclusion :=
  (compileShortcutWithCost witness conclusion premises accepted children).1

theorem compileShortcut_nodeCount {n : Nat}
    (witness : shortcutRuleInterface.W) (conclusion : Judgment)
    (premises : Fin n → Judgment)
    (accepted : shortcutRuleInterface.isInstance witness
      (List.ofFn premises) conclusion = true)
    (children : (i : Fin n) →
      AcceptedCertificate baseRuleInterface (premises i)) :
    (compileShortcut witness conclusion premises accepted children).nodeCount =
      2 + ∑ i : Fin n, (children i).nodeCount := by
  exact (compileShortcutWithCost witness conclusion premises accepted children).2

/-- The shortcut compiler exposes the exact local cost: two base rule nodes
replace each accepted shortcut node. -/
def shortcutCertificateCompiler :
    AdditionalRuleCertificateCompiler baseRuleInterface shortcutRuleInterface where
  overhead := fun _ _ _ => 2
  compileWithBound witness conclusion premises accepted children :=
    let result :=
      compileShortcutWithCost witness conclusion premises accepted children
    ⟨result.1, Nat.le_of_eq result.2⟩

inductive NewFactRuleWitness where
  | deriveD
deriving DecidableEq

def newFactRuleIsInstance (_witness : NewFactRuleWitness)
    (premises : List Judgment) (conclusion : Judgment) : Bool :=
  decide (premises = [] ∧ conclusion = .d)

/-- Exact replay interface for the genuinely new premise-free fact `d`. -/
def newFactRuleInterface : RuleWitness NewFactRule where
  W := NewFactRuleWitness
  isInstance := newFactRuleIsInstance
  sound witness premises conclusion accepted := by
    cases witness
    simp only [newFactRuleIsInstance, decide_eq_true_eq] at accepted
    rcases accepted with ⟨rfl, rfl⟩
    exact NewFactRule.d
  complete premises conclusion rule := by
    cases rule
    exact ⟨.deriveD, by decide⟩

/-- Negative control: a compiler for the new fact would manufacture a base
certificate for the known-underivable judgment `d`. -/
theorem no_newFactCertificateCompiler :
    ¬ Nonempty
      (AdditionalRuleCertificateCompiler baseRuleInterface
        newFactRuleInterface) := by
  rintro ⟨compiler⟩
  let noPremises : Fin 0 → Judgment := fun i => Fin.elim0 i
  let noChildren : (i : Fin 0) →
      AcceptedCertificate baseRuleInterface (noPremises i) :=
    fun i => Fin.elim0 i
  let compiled := compiler.compile .deriveD .d noPremises (by decide) noChildren
  apply d_not_derivable
  have derived := Derivation.valid_sound baseRuleInterface
    compiled.certificate compiled.accepted
  rw [compiled.concludes] at derived
  exact derived

/-- Accepted base axiom, retagged as a certificate for the union interface. -/
def extendedA :
    AcceptedCertificate (baseRuleInterface.sum shortcutRuleInterface)
      Judgment.a :=
  AcceptedCertificate.node
    (baseRuleInterface.sum shortcutRuleInterface)
    (.inl BaseRuleWitness.axiomA) Judgment.a
    (fun i : Fin 0 => Fin.elim0 i) (by decide)
    (fun i => Fin.elim0 i)

/-- A complete accepted source certificate using the added shortcut. -/
def shortcutSource :
    AcceptedCertificate (baseRuleInterface.sum shortcutRuleInterface)
      Judgment.c :=
  AcceptedCertificate.node
    (baseRuleInterface.sum shortcutRuleInterface)
    (.inr ShortcutRuleWitness.aToC) Judgment.c
    (fun _ : Fin 1 => Judgment.a) (by decide)
    (fun _ => extendedA)

/-- The generic compiler eliminates the shortcut from the complete source
certificate and returns a base-only certificate for the same conclusion. -/
def compiledShortcut : AcceptedCertificate baseRuleInterface Judgment.c :=
  shortcutCertificateCompiler.compileAccepted shortcutSource.certificate
    shortcutSource.accepted

/-- Positive end-to-end cost receipt for the concrete shortcut certificate. -/
theorem compiledShortcut_nodeCount_le_budget :
    compiledShortcut.nodeCount ≤
      shortcutCertificateCompiler.compilationBudget
        shortcutSource.certificate :=
  shortcutCertificateCompiler.compileAccepted_nodeCount_le
    shortcutSource.certificate shortcutSource.accepted

/-- The structural budget for the one-axiom, one-shortcut source is exactly
three base rule nodes. -/
theorem shortcutSource_compilationBudget :
    shortcutCertificateCompiler.compilationBudget
      shortcutSource.certificate = 3 := by
  rfl

theorem compiledShortcut_nodeCount_le_three :
    compiledShortcut.nodeCount ≤ 3 := by
  rw [← shortcutSource_compilationBudget]
  exact compiledShortcut_nodeCount_le_budget

end ConservativeExtensionCanary

end Mettapedia.Logic
