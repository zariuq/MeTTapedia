import Mettapedia.Languages.VibeITP.Presentation.DefinitionSignature
import Mettapedia.Languages.VibeITP.Presentation.LiteralCorrespondence

/-!
# Supplied static Vibe proofs

The finite witness selects its actual axiom or definition by position in the
theory. Modus ponens checks ordered children; instantiation retains its symbol
and value; literal leaves retain all operands. Definition leaves supply their
occurrence hints. The independent checker and relational witness judgment do
not search for a proof of the requested conclusion.

Fresh allocation and sequential theory admission are separate from checking a
proof against an existing theory. Static derivability excludes native execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs

open ComputationalDefinitions ComputationalLiterals

inductive ProofWitness where
  | axiom (index : Nat)
  | definition (index : Nat) (hints : List Nat)
  | modusPonens (implication premise : ProofWitness)
  | instantiate (symbol : Spec.SymId) (value : Spec.Term) (child : ProofWitness)
  | literal (request : LiteralRequest)
  deriving Repr

def definitionRequest (declaration : Spec.Definition) (hints : List Nat) : DefinitionRequest :=
  ⟨declaration.symbol, declaration.fvars, hints, declaration.value⟩

def modusPonensResult (implication premise : Spec.Term) : Option Spec.Term :=
  match implication with
  | .app (.builtin .impl) [antecedent, conclusion] =>
      if antecedent = premise then some conclusion else none
  | _ => none

theorem modusPonensResult_eq_some_iff (implication premise conclusion : Spec.Term) :
    modusPonensResult implication premise = some conclusion ↔
      implication = Spec.Term.impl premise conclusion := by
  cases implication with
  | bvar _ => simp [modusPonensResult, Spec.Term.impl]
  | lit _ => simp [modusPonensResult, Spec.Term.impl]
  | app symbol arguments =>
      cases symbol with
      | fresh _ => simp [modusPonensResult, Spec.Term.impl]
      | builtin builtin =>
          cases builtin <;> try simp [modusPonensResult, Spec.Term.impl]
          cases arguments with
          | nil => simp
          | cons antecedent rest =>
              cases rest with
              | nil => simp
              | cons actual rest =>
                  cases rest with
                  | nil => by_cases same : antecedent = premise <;> simp [same]
                  | cons _ _ => simp

namespace ProofWitness

def result (theory : Spec.Theory) : ProofWitness → Option Spec.Term
  | .axiom index => theory.axioms[index]?
  | .definition index hints => do
      let declaration ← theory.definitions[index]?
      (definitionRequest declaration hints).result theory.sig
  | .modusPonens implication premise => do
      let implicationStatement ← result theory implication
      let premiseStatement ← result theory premise
      modusPonensResult implicationStatement premiseStatement
  | .instantiate symbol value child => do
      let statement ← result theory child
      if Spec.WellFormed theory.sig value then
        Spec.instantiateStatement theory.sig symbol value statement
      else none
  | .literal request => request.result

inductive Checks (theory : Spec.Theory) : ProofWitness → Spec.Term → Prop where
  | axiom {index : Nat} {statement : Spec.Term} :
      theory.axioms[index]? = some statement →
      Checks theory (.axiom index) statement
  | definition {index : Nat} {hints : List Nat} {declaration : Spec.Definition} :
      theory.definitions[index]? = some declaration →
      Spec.WellFormed theory.sig declaration.value = true →
      Spec.definitionAdmissible theory.sig declaration.fvars hints declaration.value = true →
      Checks theory (.definition index hints)
        (Spec.definitionStatement theory.sig declaration.symbol declaration.fvars declaration.value)
  | modusPonens {implication premise : ProofWitness} {antecedent conclusion : Spec.Term} :
      Checks theory implication (Spec.Term.impl antecedent conclusion) →
      Checks theory premise antecedent →
      Checks theory (.modusPonens implication premise) conclusion
  | instantiate {symbol : Spec.SymId} {value statement conclusion : Spec.Term} {child : ProofWitness} :
      Checks theory child statement → Spec.WellFormed theory.sig value = true →
      Spec.instantiateStatement theory.sig symbol value statement = some conclusion →
      Checks theory (.instantiate symbol value child) conclusion
  | literal {request : LiteralRequest} {statement : Spec.Term} :
      request.result = some statement → Checks theory (.literal request) statement

theorem Checks.eval {theory : Spec.Theory} {witness : ProofWitness} {statement : Spec.Term}
    (checked : Checks theory witness statement) : result theory witness = some statement := by
  induction checked with
  | «axiom» lookup => exact lookup
  | definition lookup formed admitted =>
      simp [result, lookup, definitionRequest, DefinitionRequest.result, formed, admitted]
  | modusPonens _ _ implication premise =>
      simp [result, implication, premise, modusPonensResult, Spec.Term.impl]
  | instantiate _ formed instantiated child => simp [result, child, formed, instantiated]
  | literal authorized => exact authorized

theorem result_sound {theory : Spec.Theory} {witness : ProofWitness} {statement : Spec.Term}
    (accepted : result theory witness = some statement) : Checks theory witness statement := by
  induction witness generalizing statement with
  | «axiom» index => exact .axiom accepted
  | definition index hints =>
      cases lookup : theory.definitions[index]? with
      | none => simp [result, lookup] at accepted
      | some declaration =>
          have authorized : (definitionRequest declaration hints).result theory.sig = some statement := by
            simpa [result, lookup] using accepted
          unfold DefinitionRequest.result at authorized
          split at authorized
          next guard =>
            have guards := Bool.and_eq_true_iff.mp guard
            cases Option.some.inj authorized
            exact .definition lookup guards.1 guards.2
          next => cases authorized
  | modusPonens implication premise implicationIH premiseIH =>
      cases left : result theory implication with
      | none => simp [result, left] at accepted
      | some implicationStatement =>
          cases right : result theory premise with
          | none => simp [result, right] at accepted
          | some premiseStatement =>
              have operation : modusPonensResult implicationStatement premiseStatement = some statement := by
                simpa [result, left, right] using accepted
              have matched := (modusPonensResult_eq_some_iff _ _ _).mp operation
              have implicationChecked := implicationIH left
              rw [matched] at implicationChecked
              exact .modusPonens implicationChecked (premiseIH right)
  | instantiate symbol value child childIH =>
      cases computed : result theory child with
      | none => simp [result, computed] at accepted
      | some childStatement =>
          cases formed : Spec.WellFormed theory.sig value with
          | false => simp [result, computed, formed] at accepted
          | true =>
              exact .instantiate (childIH computed) formed
                (by simpa [result, computed, formed] using accepted)
  | literal request => exact .literal accepted

theorem result_eq_some_iff (theory : Spec.Theory) (witness : ProofWitness) (statement : Spec.Term) :
    result theory witness = some statement ↔ Checks theory witness statement := ⟨result_sound, Checks.eval⟩

theorem result_none_iff (theory : Spec.Theory) (witness : ProofWitness) :
    result theory witness = none ↔ ¬ ∃ statement, Checks theory witness statement := by
  constructor
  · intro refused ⟨statement, checked⟩
    have success := checked.eval
    rw [refused] at success
    contradiction
  · intro impossible
    cases computed : result theory witness with
    | none => rfl
    | some statement => exact False.elim (impossible ⟨statement, result_sound computed⟩)

theorem Checks.derives {theory : Spec.Theory} {witness : ProofWitness} {statement : Spec.Term}
    (checked : Checks theory witness statement) : Spec.Derives theory statement := by
  induction checked with
  | «axiom» lookup => exact .axiom (List.mem_of_getElem? lookup)
  | definition lookup _ _ => exact .definition (List.mem_of_getElem? lookup)
  | modusPonens _ _ implication premise => exact .modusPonens implication premise
  | instantiate _ formed instantiated child => exact .instantiate child formed instantiated
  | literal authorized => exact LiteralRequest.derivable theory _ authorized

theorem Checks.deterministic {theory : Spec.Theory} {witness : ProofWitness} {first second : Spec.Term}
    (left : Checks theory witness first) (right : Checks theory witness second) : first = second :=
  Option.some.inj (left.eval.symm.trans right.eval)

def check (theory : Spec.Theory) (witness : ProofWitness) (claimed : Spec.Term) : Bool :=
  decide (result theory witness = some claimed)

theorem check_iff (theory : Spec.Theory) (witness : ProofWitness) (claimed : Spec.Term) :
    check theory witness claimed = true ↔ Checks theory witness claimed := by
  simp only [check, decide_eq_true_eq, result_eq_some_iff]

theorem check_sound {theory : Spec.Theory} {witness : ProofWitness} {claimed : Spec.Term}
    (accepted : check theory witness claimed = true) : Spec.Derives theory claimed :=
  ((check_iff _ _ _).mp accepted).derives

end ProofWitness

theorem certificate_exists {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    {statement : Spec.Term} (derived : Spec.Derives theory statement) :
    ∃ witness, ProofWitness.Checks theory witness statement := by
  induction derived with
  | «axiom» member =>
      obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
      exact ⟨.axiom index, .axiom lookup⟩
  | @definition declaration member =>
      obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨_, formed, hints, admitted⟩ := hosted.definitionsOk declaration member
      exact ⟨.definition index hints, .definition lookup formed admitted⟩
  | modusPonens _ _ implicationIH premiseIH =>
      obtain ⟨implication, implicationChecked⟩ := implicationIH
      obtain ⟨premise, premiseChecked⟩ := premiseIH
      exact ⟨.modusPonens implication premise, .modusPonens implicationChecked premiseChecked⟩
  | instantiate _ formed instantiated childIH =>
      obtain ⟨child, childChecked⟩ := childIH
      exact ⟨.instantiate _ _ child, .instantiate childChecked formed instantiated⟩
  | @litIsNat value bound => exact ⟨.literal (.isNat value), .literal (by simp [LiteralRequest.result, bound])⟩
  | @litLt a b ordered bound =>
      exact ⟨.literal (.lessThan a b), .literal (by simp [LiteralRequest.result, ordered, bound])⟩
  | @litAdd a b left right =>
      exact ⟨.literal (.addition a b), .literal (by simp [LiteralRequest.result, left, right])⟩
  | @litMul a b left right =>
      exact ⟨.literal (.multiplication a b), .literal (by simp [LiteralRequest.result, left, right])⟩
  | @litDiv a b left right nonzero =>
      exact ⟨.literal (.division a b), .literal (by simp [LiteralRequest.result, left, right, nonzero])⟩
  | @litLength bytes formed =>
      have bound : bytes.length + 8 < Spec.wordBound := by simpa [Spec.WellFormed] using formed
      exact ⟨.literal (.length (.lit bytes)), .literal (by simp [LiteralRequest.result, bound])⟩
  | @litGet bytes index formed bound =>
      exact ⟨.literal (.get (.lit bytes) index), .literal (by simp_all [LiteralRequest.result, Spec.WellFormed])⟩

theorem derives_iff_checked {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (statement : Spec.Term) :
    Spec.Derives theory statement ↔ ∃ witness, ProofWitness.check theory witness statement = true := by
  constructor
  · intro derived
    obtain ⟨witness, checked⟩ := certificate_exists hosted derived
    exact ⟨witness, (ProofWitness.check_iff _ _ _).mpr checked⟩
  · rintro ⟨witness, checked⟩
    exact ProofWitness.check_sound checked

end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs
