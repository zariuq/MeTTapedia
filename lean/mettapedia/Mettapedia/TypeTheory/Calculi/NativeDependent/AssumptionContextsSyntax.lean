import Mettapedia.TypeTheory.Calculi.NativeDependent.Syntax

/-!
# Typed proof assumptions and full-motive dependent pair judgments

Raw contexts extend the fixed object-sort presentation by typed proof
assumptions. A variable retains its binding position, including beneath
object binders. Independent motive symbols may depend on the entire proof
context. The dependent pair eliminator binds both the object and its proof
before deriving a motive over the complete pair context.

The object sort remains fixed. Context extension by every generated motive
type, arbitrary-domain dependent formers and classifying CwF initiality are
not supplied by this fragment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContexts

universe u v w z

inductive Scope (Constant : Type u) (Predicate : Type v) : Nat → Type (max u v) where
  | objects (n : Nat) : Scope Constant Predicate n
  | object {n : Nat} (previous : Scope Constant Predicate n) : Scope Constant Predicate (n + 1)
  | proof {n : Nat} (previous : Scope Constant Predicate n)
      (formula : Formula Constant Predicate n) : Scope Constant Predicate n

variable {Constant : Type u} {Predicate : Type v}

/-- Variable membership is proof relevant: identically typed assumptions
occupying distinct positions are distinct variables. -/
inductive Hypothesis : {n : Nat} → Scope Constant Predicate n →
    Formula Constant Predicate n → Type (max u v) where
  | here {n : Nat} (previous : Scope Constant Predicate n) (formula : Formula Constant Predicate n) :
      Hypothesis (.proof previous formula) formula
  | proofThere {n : Nat} {previous : Scope Constant Predicate n}
      {formula : Formula Constant Predicate n} (hypothesis : Hypothesis previous formula)
      (newFormula : Formula Constant Predicate n) :
      Hypothesis (.proof previous newFormula) formula
  | objectThere {n : Nat} {previous : Scope Constant Predicate n}
      {formula : Formula Constant Predicate n} (hypothesis : Hypothesis previous formula) :
      Hypothesis (.object previous) (.substitute formula ObjectSubstitution.weaken)

namespace Hypothesis

def position : {n : Nat} → {scope : Scope Constant Predicate n} →
    {formula : Formula Constant Predicate n} → Hypothesis scope formula → Nat
  | _, _, _, .here _ _ => 0
  | _, _, _, .proofThere hypothesis _ => hypothesis.position + 1
  | _, _, _, .objectThere hypothesis => hypothesis.position

theorem duplicate_positions_differ {n : Nat} (scope : Scope Constant Predicate n)
    (formula : Formula Constant Predicate n) :
    Hypothesis.here (.proof scope formula) formula ≠
      Hypothesis.proofThere (.here scope formula) formula := by
  intro equal
  have positions := congrArg position equal
  exact Nat.zero_ne_one positions

end Hypothesis

/-- The legacy quantified types can be inhabited using actual contextual
assumptions, retained old proof syntax or a dependent pair introduction. -/
inductive ScopedEvidence
    (Declaration : (n : Nat) → Formula Constant Predicate n → Type w) :
    {n : Nat} → Scope Constant Predicate n → Formula Constant Predicate n → Type (max u v w) where
  | hypothesis {n : Nat} {scope : Scope Constant Predicate n}
      {formula : Formula Constant Predicate n} (hypothesis : Hypothesis scope formula) :
      ScopedEvidence Declaration scope formula
  | authored {n : Nat} (scope : Scope Constant Predicate n)
      {formula : Formula Constant Predicate n} (term : NativeDependent.Proof Declaration n formula) :
      ScopedEvidence Declaration scope formula
  | lam {n : Nat} {scope : Scope Constant Predicate n}
      {body : Formula Constant Predicate (n + 1)}
      (branch : ScopedEvidence Declaration (.object scope) body) :
      ScopedEvidence Declaration scope (.pi body)
  | app {n : Nat} {scope : Scope Constant Predicate n}
      {body : Formula Constant Predicate (n + 1)}
      (function : ScopedEvidence Declaration scope (.pi body)) (argument : ObjectTerm Constant n) :
      ScopedEvidence Declaration scope (.substitute body (ObjectSubstitution.instantiate argument))
  | instantiate {n : Nat} {scope : Scope Constant Predicate n}
      {body : Formula Constant Predicate (n + 1)}
      (branch : ScopedEvidence Declaration (.object scope) body) (argument : ObjectTerm Constant n) :
      ScopedEvidence Declaration scope (.substitute body (ObjectSubstitution.instantiate argument))
  | pair {n : Nat} {scope : Scope Constant Predicate n}
      {body : Formula Constant Predicate (n + 1)} (first : ObjectTerm Constant n)
      (second : ScopedEvidence Declaration scope
        (.substitute body (ObjectSubstitution.instantiate first))) :
      ScopedEvidence Declaration scope (.sigma body)

/-- Contextual dependent-function computation is an authored equation,
whose opening rule retains the ambient proof assumptions. -/
inductive EvidenceEquation
    {Declaration : (n : Nat) → Formula Constant Predicate n → Type w} :
    {n : Nat} → {scope : Scope Constant Predicate n} → {formula : Formula Constant Predicate n} →
      ScopedEvidence Declaration scope formula → ScopedEvidence Declaration scope formula → Prop where
  | refl {n : Nat} {scope : Scope Constant Predicate n} {formula : Formula Constant Predicate n}
      (term : ScopedEvidence Declaration scope formula) : EvidenceEquation term term
  | symm {n : Nat} {scope : Scope Constant Predicate n} {formula : Formula Constant Predicate n}
      {first second : ScopedEvidence Declaration scope formula} :
      EvidenceEquation first second → EvidenceEquation second first
  | trans {n : Nat} {scope : Scope Constant Predicate n} {formula : Formula Constant Predicate n}
      {first middle last : ScopedEvidence Declaration scope formula} :
      EvidenceEquation first middle → EvidenceEquation middle last → EvidenceEquation first last
  | authored {n : Nat} (scope : Scope Constant Predicate n) {formula : Formula Constant Predicate n}
      {first second : NativeDependent.Proof Declaration n formula} : ProofEquation first second →
      EvidenceEquation (.authored scope first) (.authored scope second)
  | lam {n : Nat} {scope : Scope Constant Predicate n} {body : Formula Constant Predicate (n + 1)}
      {first second : ScopedEvidence Declaration (.object scope) body} : EvidenceEquation first second →
      EvidenceEquation (.lam first) (.lam second)
  | app {n : Nat} {scope : Scope Constant Predicate n} {body : Formula Constant Predicate (n + 1)}
      {first second : ScopedEvidence Declaration scope (.pi body)} : EvidenceEquation first second →
      (argument : ObjectTerm Constant n) → EvidenceEquation (.app first argument) (.app second argument)
  | instantiate {n : Nat} {scope : Scope Constant Predicate n} {body : Formula Constant Predicate (n + 1)}
      {first second : ScopedEvidence Declaration (.object scope) body} : EvidenceEquation first second →
      (argument : ObjectTerm Constant n) → EvidenceEquation (.instantiate first argument) (.instantiate second argument)
  | pair {n : Nat} {scope : Scope Constant Predicate n} {body : Formula Constant Predicate (n + 1)}
      (argument : ObjectTerm Constant n)
      {first second : ScopedEvidence Declaration scope (.substitute body (ObjectSubstitution.instantiate argument))} :
      EvidenceEquation first second → EvidenceEquation (.pair argument first) (.pair argument second)
  | beta {n : Nat} {scope : Scope Constant Predicate n} {body : Formula Constant Predicate (n + 1)}
      (branch : ScopedEvidence Declaration (.object scope) body) (argument : ObjectTerm Constant n) :
      EvidenceEquation (.app (.lam branch) argument) (.instantiate branch argument)

/-- Structural frame substitution preserves the object tuple while
substituting actual typed proof assumptions. Both binder lifts are explicit. -/
inductive FrameSubstitution
    (Declaration : (n : Nat) → Formula Constant Predicate n → Type w) :
    {n : Nat} → Scope Constant Predicate n → Scope Constant Predicate n → Type (max u v w) where
  | identity {n : Nat} (scope : Scope Constant Predicate n) : FrameSubstitution Declaration scope scope
  | compose {n : Nat} {source middle target : Scope Constant Predicate n}
      (earlier : FrameSubstitution Declaration source middle)
      (later : FrameSubstitution Declaration middle target) :
      FrameSubstitution Declaration source target
  | dropProof {n : Nat} (scope : Scope Constant Predicate n) (formula : Formula Constant Predicate n) :
      FrameSubstitution Declaration (.proof scope formula) scope
  | supplyProof {n : Nat} {scope : Scope Constant Predicate n}
      {formula : Formula Constant Predicate n} (term : ScopedEvidence Declaration scope formula) :
      FrameSubstitution Declaration scope (.proof scope formula)
  | objectLift {n : Nat} {source target : Scope Constant Predicate n}
      (substitution : FrameSubstitution Declaration source target) :
      FrameSubstitution Declaration (.object source) (.object target)
  | proofLift {n : Nat} {source target : Scope Constant Predicate n}
      (substitution : FrameSubstitution Declaration source target)
      (formula : Formula Constant Predicate n) :
      FrameSubstitution Declaration (.proof source formula) (.proof target formula)

namespace Scope

def pair {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1)) : Scope Constant Predicate (n + 1) :=
  .proof (.object scope) body

def sum {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1)) : Scope Constant Predicate n :=
  .proof scope (.sigma body)

end Scope

/-- Context maps are authored syntax. Pair packing and unpacking carry
both binders; they are not defined by calling a semantic evaluator. -/
inductive ContextSubstitution
    (Declaration : (n : Nat) → Formula Constant Predicate n → Type w) :
    {n m : Nat} → Scope Constant Predicate n → Scope Constant Predicate m → Type (max u v w) where
  | frame {n : Nat} {source target : Scope Constant Predicate n}
      (substitution : FrameSubstitution Declaration source target) :
      ContextSubstitution Declaration source target
  | compose {n m k : Nat} {source : Scope Constant Predicate n}
      {middle : Scope Constant Predicate m} {target : Scope Constant Predicate k}
      (earlier : ContextSubstitution Declaration source middle)
      (later : ContextSubstitution Declaration middle target) :
      ContextSubstitution Declaration source target
  | pack {n : Nat} (scope : Scope Constant Predicate n) (body : Formula Constant Predicate (n + 1)) :
      ContextSubstitution Declaration (scope.pair body) (scope.sum body)
  | unpack {n : Nat} (scope : Scope Constant Predicate n) (body : Formula Constant Predicate (n + 1)) :
      ContextSubstitution Declaration (scope.sum body) (scope.pair body)

variable (Declaration : (n : Nat) → Formula Constant Predicate n → Type w)
variable (Motive : {n : Nat} → Scope Constant Predicate n → Type z)

/-- A motive symbol is indexed by an independently generated raw context.
Its interpretation may depend on every object and proof witness there. -/
inductive Family : {n : Nat} → Scope Constant Predicate n → Type (max u v w z) where
  | legacy {n : Nat} (scope : Scope Constant Predicate n) (formula : Formula Constant Predicate n) :
      Family scope
  | atom {n : Nat} {scope : Scope Constant Predicate n} (name : Motive scope) : Family scope
  | reindex {n m : Nat} {source : Scope Constant Predicate n} {target : Scope Constant Predicate m}
      (family : Family target) (substitution : ContextSubstitution Declaration source target) :
      Family source

variable {Declaration Motive}

set_option inductive.autoPromoteIndices false in
inductive Term
    (Declaration : (n : Nat) → Formula Constant Predicate n → Type w)
    (Motive : {n : Nat} → Scope Constant Predicate n → Type z)
    (Primitive : {n : Nat} → (scope : Scope Constant Predicate n) → Family Declaration Motive scope → Type z) :
    (n : Nat) → (scope : Scope Constant Predicate n) → Family Declaration Motive scope → Type (max u v w z) where
  | primitive {n : Nat} {scope : Scope Constant Predicate n} {family : Family Declaration Motive scope}
      (name : Primitive scope family) : @Term Declaration @Motive @Primitive _ scope family
  | evidence {n : Nat} {scope : Scope Constant Predicate n} {formula : Formula Constant Predicate n}
      (proof : ScopedEvidence Declaration scope formula) :
      @Term Declaration @Motive @Primitive _ scope (.legacy scope formula)
  | reindex {n m : Nat} {source : Scope Constant Predicate n} {target : Scope Constant Predicate m}
      {family : Family Declaration Motive target} (term : @Term Declaration @Motive @Primitive _ target family)
      (substitution : ContextSubstitution Declaration source target) :
      @Term Declaration @Motive @Primitive _ source (.reindex family substitution)
  | sigmaElim {n : Nat} (scope : Scope Constant Predicate n)
      (body : Formula Constant Predicate (n + 1)) (motive : Family Declaration Motive (scope.sum body))
      (branch : @Term Declaration @Motive @Primitive _ (scope.pair body) (.reindex motive (.pack scope body))) :
      @Term Declaration @Motive @Primitive _ (scope.sum body) motive

inductive TermEquation
    {Primitive : {n : Nat} → (scope : Scope Constant Predicate n) → Family Declaration Motive scope → Type z} :
    {n : Nat} → {scope : Scope Constant Predicate n} → {family : Family Declaration Motive scope} →
      Term Declaration @Motive @Primitive _ scope family → Term Declaration @Motive @Primitive _ scope family → Prop where
  | refl {n : Nat} {scope : Scope Constant Predicate n} {family : Family Declaration Motive scope}
      (term : Term Declaration @Motive @Primitive _ scope family) : TermEquation term term
  | evidence {n : Nat} {scope : Scope Constant Predicate n} {formula : Formula Constant Predicate n}
      {first second : ScopedEvidence Declaration scope formula} : EvidenceEquation first second →
      TermEquation (.evidence first) (.evidence second)
  | symm {n : Nat} {scope : Scope Constant Predicate n} {family : Family Declaration Motive scope}
      {first second : Term Declaration @Motive @Primitive _ scope family} : TermEquation first second → TermEquation second first
  | trans {n : Nat} {scope : Scope Constant Predicate n} {family : Family Declaration Motive scope}
      {first middle last : Term Declaration @Motive @Primitive _ scope family} :
      TermEquation first middle → TermEquation middle last → TermEquation first last
  | reindex {n m : Nat} {source : Scope Constant Predicate n} {target : Scope Constant Predicate m}
      {family : Family Declaration Motive target} {first second : Term Declaration @Motive @Primitive _ target family} :
      TermEquation first second → (substitution : ContextSubstitution Declaration source target) →
      TermEquation (.reindex first substitution) (.reindex second substitution)
  | sigmaElim {n : Nat} (scope : Scope Constant Predicate n) (body : Formula Constant Predicate (n + 1))
      (motive : Family Declaration Motive (scope.sum body))
      {first second : Term Declaration @Motive @Primitive _ (scope.pair body) (.reindex motive (.pack scope body))} :
      TermEquation first second →
      TermEquation (.sigmaElim scope body motive first) (.sigmaElim scope body motive second)
  | beta {n : Nat} (scope : Scope Constant Predicate n) (body : Formula Constant Predicate (n + 1))
      (motive : Family Declaration Motive (scope.sum body))
      (branch : Term Declaration @Motive @Primitive _ (scope.pair body) (.reindex motive (.pack scope body))) :
      TermEquation (.reindex (.sigmaElim scope body motive branch) (.pack scope body)) branch
  | eta {n : Nat} (scope : Scope Constant Predicate n) (body : Formula Constant Predicate (n + 1))
      (motive : Family Declaration Motive (scope.sum body)) (term : Term Declaration @Motive @Primitive _ (scope.sum body) motive) :
      TermEquation (.sigmaElim scope body motive (.reindex term (.pack scope body))) term

end Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContexts
