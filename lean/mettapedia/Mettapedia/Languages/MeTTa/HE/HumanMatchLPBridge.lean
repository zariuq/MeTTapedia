import Mettapedia.Languages.MeTTa.HE.HumanMatchModelTheory
import Mettapedia.Logic.LP.UnificationComplete

/-!
# First-order unification bridge for the human matcher

The human match/merge relation remains executable-independent.  This module
only embeds its finite atom equations into the already-verified generic LP
unification calculus, so Robinson completeness can be used as a proof tool for
model existence without mentioning either HE or LeaTTa execution.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanMatchLPBridge

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.LP

/-- Symbols and grounded payloads are distinct first-order constants.

The grounded lane uses LeaTTa's neutral payload type rather than only the HE
subtype.  This makes the bridge term algebra closed under every valuation used
by the conformance theorem while the source embedding below still inserts only
translated HE payloads. -/
inductive HumanConstant where
  | symbol : String → HumanConstant
  | grounded : Metta.Ground → HumanConstant

noncomputable instance humanConstantDecidableEq :
    DecidableEq HumanConstant := Classical.decEq _

/-- An expression node remembers its list arity. -/
inductive HumanFunction where
  | expression : Nat → HumanFunction
  deriving DecidableEq

/-- First-order signature of the human matching atom fragment. -/
def humanSignature : LPSignature where
  constants := HumanConstant
  vars := String
  relationSymbols := Empty
  relationArity := fun relation => nomatch relation
  functionSymbols := HumanFunction
  functionArity
    | .expression arity => arity

abbrev HumanTerm := Term humanSignature
abbrev HumanSubst := Subst humanSignature

instance humanVarsDecidableEq : DecidableEq humanSignature.vars := by
  change DecidableEq String
  infer_instance

noncomputable instance humanConstantsDecidableEq :
    DecidableEq humanSignature.constants := by
  change DecidableEq HumanConstant
  exact humanConstantDecidableEq

instance humanFunctionsDecidableEq :
    DecidableEq humanSignature.functionSymbols := by
  change DecidableEq HumanFunction
  infer_instance

mutual

/-- Structural embedding of one human atom into the generic first-order term
algebra. -/
def atomToTerm : Atom → HumanTerm
  | .symbol symbol => .const (.symbol symbol)
  | .var name => .var name
  | .grounded grounded => .const (.grounded (toLeaTTaGround grounded))
  | .expression atoms =>
      let terms := atomsToTerms atoms
      .app (.expression terms.length) terms.get

/-- Structural embedding of an atom list. -/
def atomsToTerms : List Atom → List HumanTerm
  | [] => []
  | atom :: atoms => atomToTerm atom :: atomsToTerms atoms

end

@[simp] theorem atomToTerm_symbol (symbol : String) :
    atomToTerm (.symbol symbol) = .const (.symbol symbol) := rfl

@[simp] theorem atomToTerm_var (name : String) :
    atomToTerm (.var name) = .var name := rfl

@[simp] theorem atomToTerm_grounded (grounded : GroundedValue) :
    atomToTerm (.grounded grounded) =
      .const (.grounded (toLeaTTaGround grounded)) := rfl

@[simp] theorem atomsToTerms_nil : atomsToTerms [] = [] := rfl

@[simp] theorem atomsToTerms_cons (atom : Atom) (atoms : List Atom) :
    atomsToTerms (atom :: atoms) = atomToTerm atom :: atomsToTerms atoms := rfl

@[simp] theorem atomsToTerms_length (atoms : List Atom) :
    (atomsToTerms atoms).length = atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [ih]

@[simp] theorem atomToTerm_expression (atoms : List Atom) :
    atomToTerm (.expression atoms) =
      .app (.expression (atomsToTerms atoms).length)
        (atomsToTerms atoms).get := rfl

/-- Decode every term of the bridge signature back into LeaTTa's neutral atom
syntax.  The signature is deliberately onto this syntax. -/
def termToMettaAtom : HumanTerm → Metta.Atom
  | .var name => .var name
  | .const (.symbol symbol) => .sym symbol
  | .const (.grounded grounded) => .gnd grounded
  | .app (.expression _) terms =>
      .expr (List.ofFn fun index => termToMettaAtom (terms index))

@[simp] theorem termToMettaAtom_var (name : String) :
    termToMettaAtom (.var name) = .var name := rfl

@[simp] theorem termToMettaAtom_symbol (symbol : String) :
    termToMettaAtom (.const (.symbol symbol)) = .sym symbol := rfl

@[simp] theorem termToMettaAtom_grounded (grounded : Metta.Ground) :
    termToMettaAtom (.const (.grounded grounded)) =
      .gnd grounded := rfl

mutual

/-- Encode every neutral MeTTa atom into the bridge term algebra. -/
def mettaAtomToTerm : Metta.Atom → HumanTerm
  | .sym symbol => .const (.symbol symbol)
  | .var name => .var name
  | .gnd grounded => .const (.grounded grounded)
  | .expr atoms =>
      let terms := mettaAtomsToTerms atoms
      .app (.expression terms.length) terms.get

/-- List companion of `mettaAtomToTerm`. -/
def mettaAtomsToTerms : List Metta.Atom → List HumanTerm
  | [] => []
  | atom :: atoms => mettaAtomToTerm atom :: mettaAtomsToTerms atoms

end

@[simp] theorem mettaAtomsToTerms_nil : mettaAtomsToTerms [] = [] := rfl

@[simp] theorem mettaAtomsToTerms_cons
    (atom : Metta.Atom) (atoms : List Metta.Atom) :
    mettaAtomsToTerms (atom :: atoms) =
      mettaAtomToTerm atom :: mettaAtomsToTerms atoms := rfl

@[simp] theorem mettaAtomsToTerms_length (atoms : List Metta.Atom) :
    (mettaAtomsToTerms atoms).length = atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [ih]

theorem mettaAtomsToTerms_eq_map (atoms : List Metta.Atom) :
    mettaAtomsToTerms atoms = List.map mettaAtomToTerm atoms := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [ih]

/-- The enlarged bridge signature is onto neutral MeTTa atoms. -/
theorem termToMettaAtom_mettaAtomToTerm (atom : Metta.Atom) :
    termToMettaAtom (mettaAtomToTerm atom) = atom := by
  induction atom with
  | sym symbol => rfl
  | var name => rfl
  | gnd grounded => rfl
  | expr atoms ih =>
      simp only [mettaAtomToTerm, termToMettaAtom]
      congr 1
      change List.ofFn
          (termToMettaAtom ∘ (mettaAtomsToTerms atoms).get) = atoms
      rw [← List.map_ofFn, List.ofFn_get, mettaAtomsToTerms_eq_map,
        List.map_map]
      change List.map
          (fun candidate =>
            termToMettaAtom (mettaAtomToTerm candidate)) atoms = atoms
      exact (List.map_congr_left ih).trans (List.map_id atoms)

/-- Decoding is injective.  In the expression case, equality of decoded lists
first fixes the arity and then exposes every recursively decoded child. -/
theorem termToMettaAtom_injective : Function.Injective termToMettaAtom := by
  intro left
  induction left with
  | var name =>
      intro right heq
      cases right with
      | var other =>
          simp only [termToMettaAtom, Metta.Atom.var.injEq] at heq
          subst other
          rfl
      | const constant => cases constant <;> simp [termToMettaAtom] at heq
      | app function terms =>
          cases function
          simp [termToMettaAtom] at heq
  | const constant =>
      intro right heq
      cases constant with
      | symbol symbol =>
          cases right with
          | var name => simp [termToMettaAtom] at heq
          | const other =>
              cases other with
              | symbol other =>
                  simp only [termToMettaAtom, Metta.Atom.sym.injEq] at heq
                  subst other
                  rfl
              | grounded grounded => simp [termToMettaAtom] at heq
          | app function terms =>
              cases function
              simp [termToMettaAtom] at heq
      | grounded grounded =>
          cases right with
          | var name => simp [termToMettaAtom] at heq
          | const other =>
              cases other with
              | symbol symbol => simp [termToMettaAtom] at heq
              | grounded other =>
                  simp only [termToMettaAtom, Metta.Atom.gnd.injEq] at heq
                  subst other
                  rfl
          | app function terms =>
              cases function
              simp [termToMettaAtom] at heq
  | app function terms ih =>
      cases function with
      | expression arity =>
          change Fin arity → HumanTerm at terms
          change ∀ index : Fin arity, ∀ {right : HumanTerm},
            termToMettaAtom (terms index) = termToMettaAtom right →
              terms index = right at ih
          intro right heq
          cases right with
          | var name => simp [termToMettaAtom] at heq
          | const constant => cases constant <;> simp [termToMettaAtom] at heq
          | app function' terms' =>
              cases function' with
              | expression arity' =>
                  change Fin arity' → HumanTerm at terms'
                  have hlists :
                      List.ofFn (fun index => termToMettaAtom (terms index)) =
                        List.ofFn
                          (fun index => termToMettaAtom (terms' index)) := by
                    exact Metta.Atom.expr.inj heq
                  have harity : arity = arity' := by
                    have hlength := congrArg List.length hlists
                    simpa using hlength
                  subst arity'
                  congr 1
                  funext index
                  apply ih index
                  exact congrFun (List.ofFn_inj.mp hlists) index

/-- Decode an LP substitution as a total MeTTa valuation. -/
def substValuation (substitution : HumanSubst) : String → Metta.Atom :=
  fun name => termToMettaAtom (substitution name)

/-- Encode a total MeTTa valuation as a first-order substitution. -/
def valuationSubst (valuation : String → Metta.Atom) : HumanSubst :=
  fun name => mettaAtomToTerm (valuation name)

@[simp] theorem substValuation_valuationSubst
    (valuation : String → Metta.Atom) :
    substValuation (valuationSubst valuation) = valuation := by
  funext name
  exact termToMettaAtom_mettaAtomToTerm (valuation name)

/-- Encoding followed by decoding is exactly the existing neutral LeaTTa
translation. -/
theorem termToMettaAtom_atomToTerm (atom : Atom) :
    termToMettaAtom (atomToTerm atom) = toLeaTTaAtom atom := by
  let AtomGoal : Atom → Prop := fun candidate =>
    termToMettaAtom (atomToTerm candidate) = toLeaTTaAtom candidate
  let ListGoal : List Atom → Prop := fun candidates =>
    List.map termToMettaAtom (atomsToTerms candidates) =
      toLeaTTaAtoms candidates
  have hrec : ∀ candidate, AtomGoal candidate := by
    apply Atom.rec (motive_1 := AtomGoal) (motive_2 := ListGoal)
    · intro symbol
      rfl
    · intro name
      rfl
    · intro grounded
      rfl
    · intro atoms ih
      dsimp only [AtomGoal]
      simp only [atomToTerm, termToMettaAtom, toLeaTTaAtom]
      congr 1
      calc
        List.ofFn
            (fun index => termToMettaAtom ((atomsToTerms atoms).get index)) =
            List.map termToMettaAtom
              (List.ofFn (atomsToTerms atoms).get) := by
                rw [List.map_ofFn]
                rfl
        _ = List.map termToMettaAtom (atomsToTerms atoms) := by
              rw [List.ofFn_get]
        _ = toLeaTTaAtoms atoms := ih
    · rfl
    · intro atom atoms ihAtom ihAtoms
      dsimp only [ListGoal] at ihAtom ihAtoms ⊢
      simp only [atomsToTerms, List.map_cons, toLeaTTaAtoms]
      rw [ihAtom, ihAtoms]
  exact hrec atom

/-- Decoding commutes with generic LP substitution. -/
theorem termToMettaAtom_applyTerm (substitution : HumanSubst) :
    ∀ term : HumanTerm,
      termToMettaAtom (substitution.applyTerm term) =
        applyClassSolution (substValuation substitution)
          (termToMettaAtom term) := by
  intro term
  induction term with
  | var name => simp [Subst.applyTerm, termToMettaAtom,
      applyClassSolution, substValuation]
  | const constant => cases constant <;>
      simp [Subst.applyTerm, termToMettaAtom, applyClassSolution]
  | app function terms ih =>
      cases function with
      | expression arity =>
          simp only [Subst.applyTerm, termToMettaAtom,
            applyClassSolution]
          congr 1
          rw [List.map_ofFn]
          apply congrArg List.ofFn
          funext index
          exact ih index

/-- Substitution commutes with the human-atom embedding. -/
theorem termToMettaAtom_apply_atomToTerm
    (substitution : HumanSubst) (atom : Atom) :
    termToMettaAtom (substitution.applyTerm (atomToTerm atom)) =
      applyClassSolution (substValuation substitution)
        (toLeaTTaAtom atom) := by
  rw [termToMettaAtom_applyTerm,
    termToMettaAtom_atomToTerm]

/-- Pure first-order equation presentation of a human binding record. -/
def bindingEquations (bindings : Bindings) :
    List (HumanTerm × HumanTerm) :=
  (bindings.assignments.map fun entry =>
      (Term.var entry.1, atomToTerm entry.2)) ++
  (bindings.equalities.map fun edge =>
      (Term.var edge.1, Term.var edge.2))

/-- Every generic unifier of the equation presentation decodes to an HE
binding model. -/
theorem bindingSatisfied_of_unifies
    {bindings : Bindings} {substitution : HumanSubst}
    (hunifies : Unifies substitution (bindingEquations bindings)) :
    HEBindingSatisfied (substValuation substitution) bindings := by
  constructor
  · intro key value hassignment
    have hequation := hunifies
      (.var key, atomToTerm value) (by
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨(key, value), hassignment, rfl⟩)
    have hdecoded := congrArg termToMettaAtom hequation
    simpa only [Subst.applyTerm_var, substValuation,
      termToMettaAtom_apply_atomToTerm] using hdecoded
  · intro left right hequality
    have hequation := hunifies
      (.var left, .var right) (by
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨(left, right), hequality, rfl⟩)
    have hdecoded := congrArg termToMettaAtom hequation
    simpa only [Subst.applyTerm_var, substValuation] using hdecoded

/-- Every MeTTa-valued model encodes back into a genuine first-order unifier.
The enlarged grounded signature is important here: no restriction on the
range of the valuation is needed. -/
theorem unifies_of_bindingSatisfied
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : HEBindingSatisfied valuation bindings) :
    Unifies (valuationSubst valuation) (bindingEquations bindings) := by
  intro equation hequation
  rcases List.mem_append.mp hequation with hassignment | hequality
  · rcases List.mem_map.mp hassignment with
      ⟨⟨key, value⟩, hmem, rfl⟩
    apply termToMettaAtom_injective
    simpa only [Subst.applyTerm_var, valuationSubst,
      termToMettaAtom_mettaAtomToTerm,
      termToMettaAtom_apply_atomToTerm,
      substValuation_valuationSubst] using
        hsatisfied.1 key value hmem
  · rcases List.mem_map.mp hequality with
      ⟨⟨left, right⟩, hmem, rfl⟩
    apply termToMettaAtom_injective
    simpa only [Subst.applyTerm_var, valuationSubst,
      termToMettaAtom_mettaAtomToTerm] using
        hsatisfied.2 left right hmem

/-- A model of the human binding equations yields a fuel-free Robinson
derivation, by the generic assumption-free completeness theorem. -/
theorem unifyDerives_of_model {bindings : Bindings}
    (hmodel : ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation bindings) :
    UnifyDerives (bindingEquations bindings) := by
  obtain ⟨valuation, hsatisfied⟩ := hmodel
  exact unifies_to_derives
    ⟨valuationSubst valuation,
      unifies_of_bindingSatisfied hsatisfied⟩

/-- A fuel-free Robinson derivation of the record equations is already a
constructive model certificate. -/
theorem has_model_of_unifyDerives {bindings : Bindings}
    (hderives : UnifyDerives (bindingEquations bindings)) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation bindings := by
  obtain ⟨substitution, hunifies⟩ := unifiable_of_derives hderives
  exact ⟨substValuation substitution,
    bindingSatisfied_of_unifies hunifies⟩

/-- For human binding records, the generic Robinson certificate is exactly
model existence—not an extra operational assumption. -/
theorem unifyDerives_iff_has_model {bindings : Bindings} :
    UnifyDerives (bindingEquations bindings) ↔
      ∃ valuation : String → Metta.Atom,
        HEBindingSatisfied valuation bindings :=
  ⟨has_model_of_unifyDerives, unifyDerives_of_model⟩

/-- Negative canary: acyclicity without reconciliation coherence cannot
manufacture a Robinson certificate. -/
theorem incompatibleAcyclicProbe_not_unifyDerives :
    ¬UnifyDerives
      (bindingEquations HumanMatchModelTheory.incompatibleAcyclicProbe) := by
  intro hderives
  exact HumanMatchModelTheory.incompatibleAcyclicProbe_has_no_model
    (has_model_of_unifyDerives hderives)

end Mettapedia.Languages.MeTTa.HE.HumanMatchLPBridge
