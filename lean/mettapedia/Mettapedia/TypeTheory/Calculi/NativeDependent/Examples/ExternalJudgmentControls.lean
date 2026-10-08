import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPremiseEvidence
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalDeclarationOrder
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalHeaderFormation
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalOrderDecision
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic.FinCases

/-!
# Variable-domain and full-motive generated judgment controls

The dependent primitive ranges over functions, rather than a fixed object sort.
Its full-pair motive has a pair-valued parameter containing both components.
All declaration headers and the supplied branch are independently formed using
the generated rules. Raw binders and retained premise occurrences have separate
negative controls.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Controls

inductive TypeSymbol where
  | scalar
  | fibre
  | pairMotive
  deriving DecidableEq

inductive TermSymbol where
  | fullBranch
  deriving DecidableEq

def symbols : Symbols where
  TypeSymbol := TypeSymbol
  TermSymbol := TermSymbol
  typeArity
    | .scalar => 0
    | .fibre => 1
    | .pairMotive => 1
  termArity := fun _ => 2

def scalar (n : Nat) : TypeExpr symbols n := .family .scalar Fin.elim0

/-- The generated dependent domain is itself a function type. -/
def domain (n : Nat) : TypeExpr symbols n := .pi (scalar n) (scalar (n + 1))

def body (n : Nat) : TypeExpr symbols (n + 1) := .family .fibre (fun _ => .var 0)

def sum (n : Nat) : TypeExpr symbols n := .sigma (domain n) (body n)

/-- This atom receives the complete pair, preserving both of its components. -/
def motive (n : Nat) : TypeExpr symbols (n + 1) := .family .pairMotive (fun _ => .var 0)

def componentContext (n : Nat) (context : ContextExpr symbols n) : ContextExpr symbols (n + 2) :=
  .snoc (.snoc context (domain n)) (body n)

def signature : Signature symbols where
  typeRank
    | .scalar => 0
    | .fibre => 2
    | .pairMotive => 4
  termRank := fun _ => 5
  typeParameters
    | .scalar => .nil
    | .fibre => .snoc .nil (domain 0)
    | .pairMotive => .snoc .nil (sum 0)
  termParameters := fun _ => componentContext 0 .nil
  termResult := fun _ => (motive 0).substitute (packSubstitution (domain 0) (body 0))
  typeParameters_before := by
    intro symbol
    cases symbol <;>
      simp [ContextExpr.before, TypeExpr.before, TermExpr.before, scalar, domain, sum, body, symbols]
  termParameters_before := by
    intro symbol
    cases symbol
    simp [componentContext, ContextExpr.before, TypeExpr.before, TermExpr.before, scalar, domain, body, symbols]
  termResult_before := by
    intro symbol
    cases symbol
    simp [motive, TypeExpr.substitute, TermExpr.substitute, packSubstitution, genericPair,
      TypeExpr.rename, TermExpr.rename, TypeExpr.before, TermExpr.before, scalar, domain, body, symbols]

@[simp] theorem scalar_rename {n m : Nat} (mapping : Renaming n m) :
    (scalar n).rename mapping = scalar m := by
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.scalar)
  funext position
  exact Fin.elim0 position

@[simp] theorem scalar_substitute {n m : Nat} (substitution : Substitution symbols n m) :
    (scalar n).substitute substitution = scalar m := by
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.scalar)
  funext position
  exact Fin.elim0 position

@[simp] theorem domain_rename {n m : Nat} (mapping : Renaming n m) :
    (domain n).rename mapping = domain m := by
  change .pi ((scalar n).rename mapping) ((scalar (n + 1)).rename (liftRenaming mapping)) = domain m
  rw [scalar_rename, scalar_rename]
  rfl

@[simp] theorem domain_substitute {n m : Nat} (substitution : Substitution symbols n m) :
    (domain n).substitute substitution = domain m := by
  change .pi ((scalar n).substitute substitution)
    ((scalar (n + 1)).substitute (liftSubstitution substitution)) = domain m
  rw [scalar_substitute, scalar_substitute]
  rfl

@[simp] theorem body_rename {n m : Nat} (mapping : Renaming n m) :
    (body n).rename (liftRenaming mapping) = body m := rfl

@[simp] theorem body_substitute {n m : Nat} (substitution : Substitution symbols n m) :
    (body n).substitute (liftSubstitution substitution) = body m := rfl

@[simp] theorem sum_substitute {n m : Nat} (substitution : Substitution symbols n m) :
    (sum n).substitute substitution = sum m := by
  change .sigma ((domain n).substitute substitution) ((body n).substitute (liftSubstitution substitution)) = sum m
  rw [domain_substitute, body_substitute]
  rfl

@[simp] theorem motive_substitute {n m : Nat} (substitution : Substitution symbols n m) :
    (motive n).substitute (liftSubstitution substitution) = motive m := rfl

def emptyContext : Derivation signature (.context .nil) :=
  deriveList .contextNil .nil

def extendContext {n : Nat} {context : ContextExpr symbols n} {type : TypeExpr symbols n}
    (previous : Derivation signature (.context context)) (formed : Derivation signature (.type context type)) :
    Derivation signature (.context (.snoc context type)) :=
  deriveList (.contextExtend context type) (.cons previous (.cons formed .nil))

def emptySubstitution {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.substitution context .nil Fin.elim0) :=
  deriveList (.substitutionNil context) (.cons (formed) (.nil))

def lookupVariable {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (index : Fin n) :
    Derivation signature (.term context (.var index) (context.lookup index)) :=
  deriveList (.variable context index) (.cons (formed) (.nil))

def extendSubstitutionProof {n m : Nat} {source : ContextExpr symbols n} {target : ContextExpr symbols m}
    {type : TypeExpr symbols m} {substitution : Substitution symbols m n} {term : TermExpr symbols n}
    (previous : Derivation signature (.substitution source target substitution))
    (formed : Derivation signature (.type target type))
    (typed : Derivation signature (.term source term (type.substitute substitution))) :
    Derivation signature (.substitution source (.snoc target type) (extendSubstitution substitution term)) :=
  deriveList (.substitutionExtend source target type substitution term)
    (.cons previous (.cons formed (.cons typed .nil)))

def scalarFormed {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) : Derivation signature (.type context (scalar n)) :=
  deriveList (.typeFamily context .scalar Fin.elim0)
    (.cons formed (.cons emptyContext (.cons (emptySubstitution formed) .nil)))

def domainFormed {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) : Derivation signature (.type context (domain n)) :=
  deriveList (.piFormation context (scalar n) (scalar (n + 1)))
    (.cons (scalarFormed formed)
      (.cons (scalarFormed (extendContext formed (scalarFormed formed))) .nil))

def functionHeader : Derivation signature (.context (.snoc .nil (domain 0))) :=
  extendContext emptyContext (domainFormed emptyContext)

def fibreFormed {n : Nat} {context : ContextExpr symbols n} {term : TermExpr symbols n}
    (formed : Derivation signature (.context context))
    (typed : Derivation signature (.term context term (domain n))) :
    Derivation signature (.type context (.family .fibre (fun _ => term))) := by
  have typed' : Derivation signature (.term context term ((domain 0).substitute Fin.elim0)) := by
    exact typed.reindex (congrArg (Judgment.term context term)
      (domain_substitute (Fin.elim0 : Substitution symbols 0 n)).symm)
  have argument := extendSubstitutionProof (emptySubstitution formed) (domainFormed emptyContext) typed'
  have argumentsSame : extendSubstitution (S := symbols) (Fin.elim0 : Substitution symbols 0 n) term =
      (fun _ : Fin 1 => term) := by
    funext index
    fin_cases index
    rfl
  have argument' := argument.reindex
    (congrArg (Judgment.substitution context (signature.typeParameters .fibre)) argumentsSame)
  exact deriveList (.typeFamily context .fibre (fun _ => term))
    (.cons formed (.cons functionHeader (.cons argument' .nil)))

def bodyFormed {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.type (.snoc context (domain n)) (body n)) := by
  have extended := extendContext formed (domainFormed formed)
  have newest : Derivation signature (.term (.snoc context (domain n)) (.var 0) (domain (n + 1))) := by
    exact (lookupVariable extended 0).reindex
      (congrArg (Judgment.term (.snoc context (domain n)) (.var 0))
        (by simp only [ContextExpr.lookup_zero, domain_rename]))
  exact fibreFormed extended newest

def sumFormed {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) : Derivation signature (.type context (sum n)) :=
  deriveList (.sigmaFormation context (domain n) (body n))
    (.cons (domainFormed formed) (.cons (bodyFormed formed) .nil))

def pairHeader : Derivation signature (.context (.snoc .nil (sum 0))) :=
  extendContext emptyContext (sumFormed emptyContext)

def motiveFormed {n : Nat} {context : ContextExpr symbols n} {term : TermExpr symbols n}
    (formed : Derivation signature (.context context))
    (typed : Derivation signature (.term context term (sum n))) :
    Derivation signature (.type context (.family .pairMotive (fun _ => term))) := by
  have typed' : Derivation signature (.term context term ((sum 0).substitute Fin.elim0)) := by
    exact typed.reindex (congrArg (Judgment.term context term)
      (sum_substitute (Fin.elim0 : Substitution symbols 0 n)).symm)
  have argument := extendSubstitutionProof (emptySubstitution formed) (sumFormed emptyContext) typed'
  have argumentsSame : extendSubstitution (S := symbols) (Fin.elim0 : Substitution symbols 0 n) term =
      (fun _ : Fin 1 => term) := by
    funext index
    fin_cases index
    rfl
  have argument' := argument.reindex
    (congrArg (Judgment.substitution context (signature.typeParameters .pairMotive)) argumentsSame)
  exact deriveList (.typeFamily context .pairMotive (fun _ => term))
    (.cons formed (.cons pairHeader (.cons argument' .nil)))

def componentContextFormed {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.context (componentContext n context)) :=
  extendContext (extendContext formed (domainFormed formed)) (bodyFormed formed)

@[simp] theorem genericPair_uniform (n : Nat) : genericPair (domain n) (body n) =
    (.pair (domain (n + 2)) (body (n + 2)) (.var 1) (.var 0) : TermExpr symbols (n + 2)) := by
  unfold genericPair
  rw [domain_rename, body_rename]

def genericPairTyped {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.term (componentContext n context) (genericPair (domain n) (body n)) (sum (n + 2))) := by
  have extended := componentContextFormed formed
  have first : Derivation signature (.term (componentContext n context) (.var 1) (domain (n + 2))) := by
    exact (lookupVariable extended (Fin.succ (0 : Fin (n + 1)))).reindex
      (by
        simp only [componentContext, ContextExpr.lookup_succ, ContextExpr.lookup_zero,
          domain_rename]
        rfl)
  have second : Derivation signature (.term (componentContext n context) (.var 0)
      ((body (n + 2)).substitute (instantiate (.var 1)))) := lookupVariable extended 0
  exact (deriveList (.pairIntroduction (componentContext n context) (domain (n + 2)) (body (n + 2)) (.var 1) (.var 0))
    (.cons (domainFormed extended) (.cons (bodyFormed extended) (.cons first (.cons second .nil))))).reindex
      (congrArg (fun value => Judgment.term (componentContext n context) value (sum (n + 2)))
        (genericPair_uniform n).symm)

def branchHeader : Derivation signature (.context (signature.termParameters .fullBranch)) :=
  componentContextFormed emptyContext

def branchResultFormed : Derivation signature
    (.type (signature.termParameters .fullBranch) (signature.termResult .fullBranch)) :=
  motiveFormed branchHeader (genericPairTyped emptyContext)

/-- The declaration's two arguments preserve both component positions. -/
def componentArguments (n : Nat) : Substitution symbols 2 (n + 2) :=
  extendSubstitution (extendSubstitution Fin.elim0 (.var 1)) (.var 0)

theorem componentArguments_lift (n : Nat) : componentArguments n =
    liftSubstitution (liftSubstitution (Fin.elim0 : Substitution symbols 0 n)) := by
  funext index
  fin_cases index <;> rfl

def componentArgumentsTyped {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.substitution (componentContext n context)
      (signature.termParameters .fullBranch) (componentArguments n)) := by
  have extended := componentContextFormed formed
  have first : Derivation signature (.term (componentContext n context) (.var 1)
      ((domain 0).substitute Fin.elim0)) := by
    have raw := lookupVariable extended (Fin.succ (0 : Fin (n + 1)))
    simp only [componentContext, ContextExpr.lookup_succ, ContextExpr.lookup_zero, domain_rename] at raw
    simpa only [Fin.succ_zero_eq_one, Nat.add_assoc, domain_substitute, componentContext] using raw
  have second : Derivation signature (.term (componentContext n context) (.var 0)
      ((body 0).substitute (extendSubstitution Fin.elim0 (.var 1)))) := lookupVariable extended 0
  exact extendSubstitutionProof
    (extendSubstitutionProof (emptySubstitution extended) (domainFormed emptyContext) first)
    (bodyFormed emptyContext) second

theorem branchResult_substitute (n : Nat) :
    (signature.termResult .fullBranch).substitute (componentArguments n) =
      (motive n).substitute (packSubstitution (domain n) (body n)) := by
  change ((motive 0).substitute (packSubstitution (domain 0) (body 0))).substitute
    (componentArguments n) = _
  rw [componentArguments_lift,
    TypeExpr.pairMotive_substitute (Fin.elim0 : Substitution symbols 0 n),
    domain_substitute, body_substitute, motive_substitute]

def fullBranch (n : Nat) : TermExpr symbols (n + 2) := .primitive .fullBranch (componentArguments n)

def fullBranchTyped {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.term (componentContext n context) (fullBranch n)
      ((motive n).substitute (packSubstitution (domain n) (body n)))) := by
  have branch : Derivation signature (.term (componentContext n context) (fullBranch n)
      ((signature.termResult .fullBranch).substitute (componentArguments n))) :=
    deriveList (.primitive (componentContext n context) .fullBranch (componentArguments n))
      (.cons (componentContextFormed formed) (.cons branchHeader
        (.cons branchResultFormed (.cons (componentArgumentsTyped formed) .nil))))
  simpa only [branchResult_substitute] using branch

@[simp] theorem sum_rename {n m : Nat} (mapping : Renaming n m) :
    (sum n).rename mapping = sum m := by
  change .sigma ((domain n).rename mapping) ((body n).rename (liftRenaming mapping)) = sum m
  rw [domain_rename, body_rename]
  rfl

def pairContextMotiveFormed {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.type (.snoc context (sum n)) (motive n)) := by
  have extended := extendContext formed (sumFormed formed)
  have newest : Derivation signature (.term (.snoc context (sum n)) (.var 0) (sum (n + 1))) := by
    simpa only [ContextExpr.lookup_zero, sum_rename] using lookupVariable extended 0
  exact motiveFormed extended newest

def fullElimination {n : Nat} (pair : TermExpr symbols n) : TermExpr symbols n :=
  .sigmaElim (domain n) (body n) (motive n) (fullBranch n) pair

def fullEliminationTyped {n : Nat} {context : ContextExpr symbols n} {pair : TermExpr symbols n}
    (formed : Derivation signature (.context context)) (typed : Derivation signature (.term context pair (sum n))) :
    Derivation signature (.term context (fullElimination pair) ((motive n).substitute (instantiate pair))) :=
  deriveList (.sigmaElimination context (domain n) (body n) (motive n) (fullBranch n) pair)
    (.cons (domainFormed formed) (.cons (bodyFormed formed)
      (.cons (pairContextMotiveFormed formed) (.cons (fullBranchTyped formed) (.cons typed .nil)))))

def fullMotiveFunction : TermExpr symbols 0 :=
  .lam (sum 0) (motive 0) (fullElimination (.var 0))

/-- A closed generated function uses an arbitrary function-valued first
component, a dependent second component, and a motive over the complete pair. -/
def fullMotiveFunctionTyped : Derivation signature
    (.term .nil fullMotiveFunction (.pi (sum 0) (motive 0))) := by
  have newest : Derivation signature (.term (.snoc .nil (sum 0)) (.var 0) (sum 1)) := by
    simpa only [ContextExpr.lookup_zero, sum_rename] using lookupVariable pairHeader 0
  exact deriveList (.lambda .nil (sum 0) (motive 0) (fullElimination (.var 0)))
    (.cons (sumFormed emptyContext) (.cons (pairContextMotiveFormed emptyContext)
      (.cons (fullEliminationTyped pairHeader newest) .nil)))

def newestPairTyped {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.term (.snoc context (sum n)) (.var 0) (sum (n + 1))) := by
  simpa only [ContextExpr.lookup_zero, sum_rename] using
    lookupVariable (extendContext formed (sumFormed formed)) 0

def fullMotiveBeta {n : Nat} {context : ContextExpr symbols n} {pair : TermExpr symbols n}
    (formed : Derivation signature (.context context))
    (typed : Derivation signature (.term context pair (sum n))) :
    Derivation signature (.termEq context
      (.app (sum n) (motive n) (.lam (sum n) (motive n) (fullElimination (.var 0))) pair)
      ((fullElimination (.var 0 : TermExpr symbols (n + 1))).substitute (instantiate pair))
      ((motive n).substitute (instantiate pair))) :=
  deriveList (.piBeta context (sum n) (motive n) (fullElimination (.var 0)) pair)
    (.cons (sumFormed formed) (.cons (pairContextMotiveFormed formed)
      (.cons (fullEliminationTyped (extendContext formed (sumFormed formed)) (newestPairTyped formed))
        (.cons typed .nil))))

/-- Eta for the complete pair-context motive retains an arbitrary authored
term over that context, rather than only a constant result family. -/
def fullMotiveEta {n : Nat} {context : ContextExpr symbols n} {pair : TermExpr symbols n}
    (formed : Derivation signature (.context context))
    (typed : Derivation signature (.term context pair (sum n))) :
    Derivation signature (.termEq context
      (.sigmaElim (domain n) (body n) (motive n)
        ((fullElimination (.var 0 : TermExpr symbols (n + 1))).substitute
          (packSubstitution (domain n) (body n))) pair)
      ((fullElimination (.var 0 : TermExpr symbols (n + 1))).substitute (instantiate pair))
      ((motive n).substitute (instantiate pair))) :=
  deriveList (.sigmaEliminationEta context (domain n) (body n) (motive n)
      (fullElimination (.var 0)) pair)
    (.cons (domainFormed formed) (.cons (bodyFormed formed)
      (.cons (pairContextMotiveFormed formed)
        (.cons (fullEliminationTyped (extendContext formed (sumFormed formed)) (newestPairTyped formed))
          (.cons typed .nil)))))

def firstComponentTyped : Derivation signature
    (.term (componentContext 0 .nil) (.var 1) (domain 2)) := by
  have raw := lookupVariable (componentContextFormed emptyContext) (Fin.succ (0 : Fin 1))
  simp only [componentContext, ContextExpr.lookup_succ, ContextExpr.lookup_zero, domain_rename] at raw
  simpa only [Fin.succ_zero_eq_one, componentContext, Nat.reduceAdd] using raw

def secondComponentTyped : Derivation signature
    (.term (componentContext 0 .nil) (.var 0)
      ((body 2).substitute (instantiate (.var 1)))) :=
  lookupVariable (componentContextFormed emptyContext) 0

/-- The beta result substitutes both actual components into the supplied
two-binder branch. The motive receives their complete dependent pair. -/
def fullPairBeta : Derivation signature (.termEq (componentContext 0 .nil)
    (fullElimination (.pair (domain 2) (body 2) (.var 1) (.var 0)))
    ((fullBranch 2).substitute (instantiateComponents (.var 1) (.var 0)))
    ((motive 2).substitute (instantiate (.pair (domain 2) (body 2) (.var 1) (.var 0))))) :=
  deriveList (.sigmaEliminationBeta (componentContext 0 .nil)
      (domain 2) (body 2) (motive 2) (fullBranch 2) (.var 1) (.var 0))
    (.cons (domainFormed (componentContextFormed emptyContext))
      (.cons (bodyFormed (componentContextFormed emptyContext))
        (.cons (pairContextMotiveFormed (componentContextFormed emptyContext))
          (.cons (fullBranchTyped (componentContextFormed emptyContext))
            (.cons firstComponentTyped (.cons secondComponentTyped .nil))))))

def etaFunction : TermExpr symbols 1 := .lam (scalar 1) (scalar 2)
  (.app (scalar 2) (scalar 3) (.var 1) (.var 0))

def etaFunctionEquality : Derivation signature
    (.termEq (.snoc .nil (domain 0)) etaFunction (.var 0) (domain 1)) := by
  have newest : Derivation signature (.term (.snoc .nil (domain 0)) (.var 0) (domain 1)) := by
    simpa only [ContextExpr.lookup_zero, domain_rename] using lookupVariable functionHeader 0
  simpa only [RuleCode.conclusion, TermExpr.rename, scalar_rename, etaFunction, domain,
    Fin.succ_zero_eq_one, Nat.reduceAdd] using
    deriveList (.piEta (.snoc .nil (domain 0)) (scalar 1) (scalar 2) (.var 0))
      (.cons (scalarFormed functionHeader)
        (.cons (scalarFormed (extendContext functionHeader (scalarFormed functionHeader)))
          (.cons newest .nil)))

theorem etaFunction_codes_differ : etaFunction ≠ (.var 0 : TermExpr symbols 1) := by
  intro same
  cases same

def duplicateContext : ContextExpr symbols 2 := .snoc (.snoc .nil (scalar 0)) (scalar 1)

def duplicateContextFormed : Derivation signature (.context duplicateContext) :=
  extendContext (extendContext emptyContext (scalarFormed emptyContext))
    (scalarFormed (extendContext emptyContext (scalarFormed emptyContext)))

def duplicateNewest : Derivation signature (.term duplicateContext (.var 0) (scalar 2)) := by
  simpa only [duplicateContext, ContextExpr.lookup_zero, scalar_rename] using
    lookupVariable duplicateContextFormed 0

def duplicateOlder : Derivation signature (.term duplicateContext (.var 1) (scalar 2)) := by
  have raw := lookupVariable duplicateContextFormed (Fin.succ (0 : Fin 1))
  simp only [duplicateContext, ContextExpr.lookup_succ, ContextExpr.lookup_zero, scalar_rename] at raw
  simpa only [Fin.succ_zero_eq_one, duplicateContext, Nat.reduceAdd] using raw

theorem duplicate_variable_positions_differ :
    (.var 0 : TermExpr symbols 2) ≠ .var 1 := by
  intro same
  have indices := TermExpr.var.inj same
  have values := congrArg Fin.val indices
  contradiction

theorem branch_component_order :
    componentArguments 0 0 = (.var 0 : TermExpr symbols 2) ∧
      componentArguments 0 1 = (.var 1 : TermExpr symbols 2) := ⟨rfl, rfl⟩

theorem branch_motive_uses_complete_pair :
    signature.termResult .fullBranch =
      (.family .pairMotive (fun _ => .pair (domain 2) (body 2) (.var 1) (.var 0)) :
        TypeExpr symbols 2) := by
  change TypeExpr.family (S := symbols) .pairMotive (fun _ => genericPair (domain 0) (body 0)) = _
  rw [genericPair_uniform]

theorem double_lift_protects_both_components
    (substitution : Substitution symbols 1 1) :
    liftSubstitution (liftSubstitution substitution) 0 = (.var 0 : TermExpr symbols 3) ∧
      liftSubstitution (liftSubstitution substitution) 1 = (.var 1 : TermExpr symbols 3) :=
  ⟨rfl, rfl⟩

theorem double_lift_shifts_older_argument
    (substitution : Substitution symbols 1 1) :
    liftSubstitution (liftSubstitution substitution) 2 =
      ((substitution 0).rename Fin.succ).rename Fin.succ := rfl

theorem substitution_without_binder_lifting_captures :
    ((.var 0 : TermExpr symbols 3).substitute
      (fun _ => (.var 2 : TermExpr symbols 3))) ≠
      (.var 0 : TermExpr symbols 3) := by
  intro same
  have indices := TermExpr.var.inj same
  have values := congrArg Fin.val indices
  contradiction

theorem rank_zero_cannot_have_a_nonempty_header :
    ¬ (ContextExpr.snoc (.nil : ContextExpr symbols 0) (domain 0)).before
      signature.typeRank signature.termRank 0 :=
  ContextExpr.extension_not_before_zero .nil (domain 0) signature.typeRank signature.termRank

def etaFunctionTyped : Derivation signature
    (.term (.snoc .nil (domain 0)) etaFunction (domain 1)) := by
  have extended := extendContext functionHeader (scalarFormed functionHeader)
  have older : Derivation signature
      (.term (.snoc (.snoc .nil (domain 0)) (scalar 1)) (.var 1) (domain 2)) := by
    have raw := lookupVariable extended (Fin.succ (0 : Fin 1))
    simp only [ContextExpr.lookup_succ, ContextExpr.lookup_zero, domain_rename] at raw
    simpa only [Fin.succ_zero_eq_one, Nat.reduceAdd] using raw
  have newest : Derivation signature
      (.term (.snoc (.snoc .nil (domain 0)) (scalar 1)) (.var 0) (scalar 2)) := by
    simpa only [ContextExpr.lookup_zero, scalar_rename] using lookupVariable extended 0
  have applied := deriveList
    (.application (.snoc (.snoc .nil (domain 0)) (scalar 1)) (scalar 2) (scalar 3) (.var 1) (.var 0))
    (.cons (scalarFormed extended)
      (.cons (scalarFormed (extendContext extended (scalarFormed extended)))
        (.cons older (.cons newest .nil))))
  have applied' : Derivation signature
      (.term (.snoc (.snoc .nil (domain 0)) (scalar 1))
        (.app (scalar 2) (scalar 3) (.var 1) (.var 0)) (scalar 2)) := by
    simpa only [RuleCode.conclusion, scalar_substitute] using applied
  exact deriveList (.lambda (.snoc .nil (domain 0)) (scalar 1) (scalar 2)
    (.app (scalar 2) (scalar 3) (.var 1) (.var 0)))
    (.cons (scalarFormed functionHeader) (.cons (scalarFormed extended) (.cons applied' .nil)))

def originalFamily : TypeExpr symbols 1 := .family .fibre (fun _ => .var 0)

def etaFamily : TypeExpr symbols 1 := .family .fibre (fun _ => etaFunction)

def originalFamilyFormed : Derivation signature
    (.type (.snoc .nil (domain 0)) originalFamily) := by
  have newest : Derivation signature (.term (.snoc .nil (domain 0)) (.var 0) (domain 1)) := by
    simpa only [ContextExpr.lookup_zero, domain_rename] using lookupVariable functionHeader 0
  exact fibreFormed functionHeader newest

def etaFamilyFormed : Derivation signature
    (.type (.snoc .nil (domain 0)) etaFamily) :=
  fibreFormed functionHeader etaFunctionTyped

/-- A genuine dependent primitive takes equal but syntactically different
function arguments. Its generated family congruence retains their actual use. -/
def etaFamilyEquality : Derivation signature
    (.typeEq (.snoc .nil (domain 0)) originalFamily etaFamily) := by
  have initialEquality := deriveList
    (.substitutionReflexivity (.snoc .nil (domain 0)) .nil Fin.elim0)
    (.cons (emptySubstitution functionHeader) .nil)
  have symmetric := deriveList
    (.termSymmetry (.snoc .nil (domain 0)) etaFunction (.var 0) (domain 1))
    (.cons etaFunctionEquality .nil)
  have symmetric' : Derivation signature (.termEq (.snoc .nil (domain 0))
      (.var 0) etaFunction ((domain 0).substitute Fin.elim0)) := by
    simpa only [domain_substitute] using symmetric
  have eta' : Derivation signature (.term (.snoc .nil (domain 0)) etaFunction
      ((domain 0).substitute Fin.elim0)) := by
    simpa only [domain_substitute] using etaFunctionTyped
  have argumentEquality := deriveList
    (.substitutionExtendEquality (.snoc .nil (domain 0)) .nil (domain 0)
      Fin.elim0 Fin.elim0 (.var 0) etaFunction)
    (.cons initialEquality (.cons (domainFormed emptyContext) (.cons symmetric' (.cons eta' .nil))))
  have originalArguments : extendSubstitution (S := symbols)
      (Fin.elim0 : Substitution symbols 0 1) (.var 0) = (fun _ : Fin 1 => .var 0) := by
    funext position
    fin_cases position
    rfl
  have etaArguments : extendSubstitution (S := symbols)
      (Fin.elim0 : Substitution symbols 0 1) etaFunction = (fun _ : Fin 1 => etaFunction) := by
    funext position
    fin_cases position
    rfl
  change Derivation signature (.substitutionEq (.snoc .nil (domain 0))
    (.snoc .nil (domain 0)) (extendSubstitution Fin.elim0 (.var 0))
      (extendSubstitution Fin.elim0 etaFunction)) at argumentEquality
  rw [originalArguments, etaArguments] at argumentEquality
  exact deriveList (.familyCongruence (.snoc .nil (domain 0)) .fibre
    (fun _ => .var 0) (fun _ => etaFunction))
    (.cons functionHeader (.cons argumentEquality .nil))

theorem equal_family_annotations_have_distinct_codes : originalFamily ≠ etaFamily := by
  intro same
  have arguments := eq_of_heq (TypeExpr.family.inj same).2
  have functions := congrFun arguments (0 : Fin 1)
  exact etaFunction_codes_differ functions.symm

/-- Changing a dependent domain annotation uses local type and body equations
and the actual second-side binder admission. -/
def lambdaAnnotationEquality : Derivation signature (.termEq (.snoc .nil (domain 0))
    (.lam originalFamily (domain 2) (.var 1))
    (.lam etaFamily (domain 2) (.var 1)) (.pi originalFamily (domain 2))) := by
  have firstContext := extendContext functionHeader originalFamilyFormed
  have secondContext := extendContext functionHeader etaFamilyFormed
  have firstBody := domainFormed firstContext
  have secondBody := domainFormed secondContext
  have firstValue : Derivation signature (.term
      (.snoc (.snoc .nil (domain 0)) originalFamily) (.var 1) (domain 2)) := by
    have raw := lookupVariable firstContext (Fin.succ (0 : Fin 1))
    simp only [ContextExpr.lookup_succ, ContextExpr.lookup_zero, domain_rename] at raw
    simpa only [Fin.succ_zero_eq_one, Nat.reduceAdd] using raw
  have secondValue : Derivation signature (.term
      (.snoc (.snoc .nil (domain 0)) etaFamily) (.var 1) (domain 2)) := by
    have raw := lookupVariable secondContext (Fin.succ (0 : Fin 1))
    simp only [ContextExpr.lookup_succ, ContextExpr.lookup_zero, domain_rename] at raw
    simpa only [Fin.succ_zero_eq_one, Nat.reduceAdd] using raw
  exact deriveList (.lambdaAnnotationCongruence (.snoc .nil (domain 0))
      originalFamily etaFamily (domain 2) (domain 2) (.var 1) (.var 1))
    (.cons etaFamilyEquality
      (.cons (deriveList (.typeReflexivity (.snoc (.snoc .nil (domain 0)) originalFamily) (domain 2))
          (.cons firstBody .nil))
        (.cons secondBody
          (.cons (deriveList (.termReflexivity (.snoc (.snoc .nil (domain 0)) originalFamily)
              (.var 1) (domain 2)) (.cons firstValue .nil)) (.cons secondValue .nil)))))

theorem converted_lambdas_have_distinct_codes :
    (.lam originalFamily (domain 2) (.var 1) : TermExpr symbols 1) ≠
      .lam etaFamily (domain 2) (.var 1) := by
  intro same
  exact equal_family_annotations_have_distinct_codes (TermExpr.lam.inj same).1

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Controls
