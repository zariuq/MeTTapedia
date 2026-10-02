import Mettapedia.Logic.LP.EquationalInterpretations

/-!
# Relational-chain controls for the first-order bridge

The language has primitive relation programs, binary chaining, and a nullary
identity program. Its denotation follows the earlier-then-later direction of
native hypothesis chaining: a middle value witnesses the two constituent edges.

Reassociation preserves relation support under every substitution and at every
term occurrence. Dropping a guard or reversing the constituents does not. The
same reassociation equation is invalid for the free Herbrand interpretation:
program syntax and interpreted relation support are different observations.

For Herbrand interpretations the law is used through the interpretations that
respect it. The ground programs that reach `1` from `0` form one: reassociating
a program never changes its membership, although the two programs are
different terms. The interpretation that looks at the bracketing does not
respect the law, and there reassociation does change membership.

These controls do not identify differently bracketed proof terms, quotient
duplicates, or change the runtime's quotation, branch order, effects, or cost.
-/

namespace Mettapedia.Logic.LP.FirstOrderChainControls

open FirstOrderBridge FirstOrderRewriting

inductive ProgramSymbol where
  | chain
  | identity

abbrev signature : LPSignature where
  constants := Fin 2
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 1
  functionSymbols := ProgramSymbol
  functionArity
    | .chain => 2
    | .identity => 0

abbrev Relation := Nat → Nat → Prop

/-- Perform the earlier relation first, retaining the middle-value witness. -/
def compose (earlier later : Relation) : Relation :=
  fun source target => ∃ middle, earlier source middle ∧ later middle target

theorem compose_associative (first second third : Relation) :
    compose (compose first second) third = compose first (compose second third) := by
  funext source target
  apply propext
  constructor
  · rintro ⟨laterMiddle, ⟨earlierMiddle, firstStep, secondStep⟩, thirdStep⟩
    exact ⟨earlierMiddle, firstStep, laterMiddle, secondStep, thirdStep⟩
  · rintro ⟨earlierMiddle, firstStep, laterMiddle, secondStep, thirdStep⟩
    exact ⟨laterMiddle, ⟨earlierMiddle, firstStep, secondStep⟩, thirdStep⟩

def advance : Relation := fun source target => target = source + 1

def guardOne : Relation := fun source target => source = 1 ∧ target = source

/-- The two primitives are a graph hop and an acceptance guard. -/
def primitive (symbol : Fin 2) : Relation := if symbol = 0 then advance else guardOne

private def interpretFunction : {arity : Nat} → FunctionSymbol signature arity →
    (Fin arity → Relation) → Relation
  | _, .constant symbol, _ => primitive symbol
  | _, .function ProgramSymbol.chain, arguments => compose (arguments 0) (arguments 1)
  | _, .function ProgramSymbol.identity, _ => fun source target => target = source

instance relationStructure : (language signature).Structure Relation where
  funMap := interpretFunction
  RelMap
    | .relation _, arguments => arguments 0 0 1

def chain (earlier later : Term signature) : Term signature :=
  .app .chain ![earlier, later]

def associativity : Equation signature where
  left := chain (chain (.var 0) (.var 1)) (.var 2)
  right := chain (.var 0) (chain (.var 1) (.var 2))

theorem associativity_valid : associativity.Valid Relation := by
  intro assignment
  change compose (compose (assignment 0) (assignment 1)) (assignment 2) =
    compose (assignment 0) (compose (assignment 1) (assignment 2))
  exact compose_associative _ _ _

/-- A real Rw certificate: reassociation is instantiated inside the supplied
program context, rather than asserted separately for each graph query. -/
theorem reassociation (context : Context signature) (substitution : Subst signature) :
    Rewrite {associativity} (context.fill (substitution.applyTerm associativity.left))
      (context.fill (substitution.applyTerm associativity.right)) :=
  Rewrite.rule associativity (Set.mem_singleton _) substitution context

theorem contextual_reassociation (context : Context signature)
    (substitution : Subst signature) (assignment : signature.vars → Relation) :
    realizeTerm assignment (context.fill (substitution.applyTerm associativity.left)) =
      realizeTerm assignment (context.fill (substitution.applyTerm associativity.right)) := by
  apply rewrite_sound (rules := {associativity})
  · intro equation member
    have same := Set.mem_singleton_iff.mp member
    subst equation
    exact associativity_valid
  · exact reassociation context substitution

def reachable (program : Term signature) : Atom signature := ⟨(), ![program]⟩

theorem reassociation_preserves_query (substitution : Subst signature)
    (assignment : signature.vars → Relation) :
    realizeAtom assignment (reachable (substitution.applyTerm associativity.left)) ↔
      realizeAtom assignment (reachable (substitution.applyTerm associativity.right)) := by
  change realizeTerm assignment (substitution.applyTerm associativity.left) 0 1 ↔
    realizeTerm assignment (substitution.applyTerm associativity.right) 0 1
  have same := contextual_reassociation .hole substitution assignment
  change realizeTerm assignment (substitution.applyTerm associativity.left) =
    realizeTerm assignment (substitution.applyTerm associativity.right) at same
  rw [same]

theorem advance_then_guard : compose advance guardOne 0 1 := by
  exact ⟨1, rfl, rfl, rfl⟩

theorem guard_then_advance_fails : ¬compose guardOne advance 0 1 := by
  rintro ⟨_, ⟨impossible, _⟩, _⟩
  exact Nat.zero_ne_one impossible

theorem reordering_chain_invalid :
    ¬(Equation.mk (chain (.const 0) (.const 1)) (chain (.const 1) (.const 0))).Valid Relation := by
  intro valid
  have same := valid (fun _ => advance)
  change compose advance guardOne = compose guardOne advance at same
  exact guard_then_advance_fails (same ▸ advance_then_guard)

theorem dropping_guard_invalid :
    ¬(Equation.mk (chain (.const 0) (.const 1)) (.const 0)).Valid Relation := by
  intro valid
  have same := valid (fun _ => advance)
  change compose advance guardOne = advance at same
  have accepted : compose advance guardOne 2 3 := same.symm ▸ (rfl : advance 2 3)
  obtain ⟨middle, _, impossible, _⟩ := accepted
  omega

/-- A constant does not acquire the tag of a nullary function during encoding. -/
theorem constant_not_nullary_function :
    encodeTerm (Term.const (0 : Fin 2) : Term signature) ≠
      encodeTerm (Term.app ProgramSymbol.identity Fin.elim0 : Term signature) := by
  intro same
  have impossible := encodeTerm_injective same
  cases impossible

private def leftArgumentIsChain : GroundTerm signature → Bool
  | .const _ => false
  | .app .identity _ => false
  | .app .chain arguments =>
    match arguments 0 with
    | .const _ => false
    | .app .identity _ => false
    | .app .chain _ => true

/-- The denotational optimization cannot be advertised as an equation of
opaque program syntax, even though relation support satisfies it universally. -/
theorem associativity_not_herbrand_valid (interpretation : Interpretation signature) :
    let := herbrandStructure interpretation
    ¬associativity.Valid (GroundTerm signature) := by
  dsimp only
  let _ := herbrandStructure interpretation
  intro valid
  have same := valid (fun _ => GroundTerm.const 0)
  have different := congrArg leftArgumentIsChain same
  change true = false at different
  cases different

/-- The chain signature has two distinct ground terms, so the free
interpretation validates identities only: no rule that changes a program is
an equation of program syntax. -/
theorem herbrand_valid_iff_identity (interpretation : Interpretation signature)
    (equation : Equation signature) :
    (let := herbrandStructure interpretation
     equation.Valid (GroundTerm signature)) ↔ equation.left = equation.right := by
  constructor
  · exact equation.eq_of_valid_herbrand interpretation
      (first := GroundTerm.const 0) (second := GroundTerm.const 1)
      (fun same => absurd (GroundTerm.const.inj same) (by decide))
  · intro identity
    dsimp only
    intro assignment
    rw [identity]

/-! ## Interpretations that respect reassociation, and one that does not -/

/-- The ground programs that reach `1` from `0`. -/
def reaching : Interpretation signature := inducedInterpretation Relation

theorem associativity_rules_valid :
    ∀ equation ∈ ({associativity} : Set (Equation signature)), equation.Valid Relation := by
  intro equation member
  rw [Set.mem_singleton_iff.mp member]
  exact associativity_valid

/-- The reaching programs respect reassociation. -/
theorem reaching_respects : Respects {associativity} reaching :=
  respects_inducedInterpretation associativity_rules_valid

/-- **Reassociating a program, under any substitution and any grounding,
never changes whether it reaches `1` from `0`.** -/
theorem reassociation_preserves_membership (substitution : Subst signature)
    (grounding : Grounding signature) :
    grounding.groundAtom (reachable (substitution.applyTerm associativity.left)) ∈ reaching ↔
      grounding.groundAtom (reachable (substitution.applyTerm associativity.right)) ∈ reaching := by
  have step := rewrite_groundAtom_iff reaching_respects
    (reachable (substitution.applyTerm associativity.left)) 0
    (substitution.applyTerm associativity.right) (reassociation .hole substitution) grounding
  have updated : (⟨(), Function.update ![substitution.applyTerm associativity.left] 0
      (substitution.applyTerm associativity.right)⟩ : Atom signature) =
      reachable (substitution.applyTerm associativity.right) := by
    unfold reachable
    congr 1
    funext index
    fin_cases index
    simp
  exact updated ▸ step

/-- The two sides of the law are different terms: the statement above is not
about replacing a term by itself. -/
theorem associativity_sides_differ : associativity.left ≠ associativity.right := by
  intro same
  have image := congrArg
    (Grounding.groundTerm (σ := signature) fun _ => GroundTerm.const 0) same
  have different := congrArg leftArgumentIsChain image
  change true = false at different
  cases different

/-- Advance, then the guard, then the identity. -/
def advanceGuardIdentity : GroundTerm signature :=
  .app .chain ![.app .chain ![.const 0, .const 1], .app .identity Fin.elim0]

/-- The same three programs, bracketed to the right. -/
def advanceThenGuardIdentity : GroundTerm signature :=
  .app .chain ![.const 0, .app .chain ![.const 1, .app .identity Fin.elim0]]

/-- Both bracketings reach `1` from `0`, and they are different programs. -/
theorem both_bracketings_reach :
    (⟨(), ![advanceGuardIdentity]⟩ : GroundAtom signature) ∈ reaching ∧
      (⟨(), ![advanceThenGuardIdentity]⟩ : GroundAtom signature) ∈ reaching ∧
      advanceGuardIdentity ≠ advanceThenGuardIdentity := by
  refine ⟨?_, ?_, ?_⟩
  · change compose (compose advance guardOne) (fun source target => target = source) 0 1
    exact ⟨1, advance_then_guard, rfl⟩
  · change compose advance (compose guardOne (fun source target => target = source)) 0 1
    exact ⟨1, rfl, 1, ⟨rfl, rfl⟩, rfl⟩
  · intro same
    have different := congrArg leftArgumentIsChain same
    change true = false at different
    cases different

/-- The ground programs whose first constituent is itself a chain. -/
def leftNested : Interpretation signature :=
  {atom | leftArgumentIsChain (atom.args 0) = true}

/-- **An interpretation that looks at the bracketing does not respect
reassociation.** -/
theorem leftNested_not_respects : ¬ Respects {associativity} leftNested := by
  intro respects
  have congruent : AtomCongruent {associativity}
      (⟨(), fun _ => Grounding.groundTerm (fun _ => GroundTerm.const 0) associativity.left⟩ :
        GroundAtom signature)
      ⟨(), fun _ => Grounding.groundTerm (fun _ => GroundTerm.const 0) associativity.right⟩ :=
    .arguments () fun _ =>
      GroundCongruent.rule (rules := {associativity}) associativity (Set.mem_singleton _)
        (fun _ => GroundTerm.const 0)
  have member := respects congruent (show leftArgumentIsChain _ = true from rfl)
  change false = true at member
  cases member

/-- So there reassociation changes membership. -/
theorem leftNested_not_rewriteInvariant : ¬ RewriteInvariant {associativity} leftNested :=
  fun invariant => leftNested_not_respects invariant.respects

end Mettapedia.Logic.LP.FirstOrderChainControls
