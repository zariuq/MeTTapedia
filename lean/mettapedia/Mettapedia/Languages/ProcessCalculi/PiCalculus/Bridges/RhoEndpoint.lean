import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingStepRF
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredRFComparison
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness

/-!
# Actual communication endpoints of the maintained pi-to-rho compiler

Networks are lists of the existing named processes. Their compilation is a
parallel bag of the existing compiler's outputs. Occurrence selection retains
multiplicity; the correspondence relates the contractum of the supplied rho
firing, rather than a separately selected successful execution.

The comparison covers restriction- and replication-free communication
components under the explicit variable convention. The unrestricted
name-server and arbitrary structural-representative reflection problems are
separate.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus hiding StructuralCongruence NameEquiv
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
  (rhoStepAt_one_comm apply_commBindingsAt)

local notation:50 p " ≡ᵨ " q =>
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p q

/-- Flatten only active source parallel composition. Input bodies remain
guarded and are released by communication. -/
def components : Process → List Process
  | .nil => []
  | .par left right => components left ++ components right
  | process => [process]

/-- Assemble existing named processes using their existing parallel operator. -/
def assemble (processes : List Process) : Process :=
  processes.foldr Process.par .nil

/-- A communication component has no active parallel wrapper; its guarded
continuation may be any restriction- and replication-free process. -/
def Atom : Process → Prop
  | .input _ _ body => RestrictionFree body
  | .output _ _ => True
  | _ => False

def Flat (processes : List Process) : Prop := ∀ process ∈ processes, Atom process

/-- Compile a component list with the maintained compiler, retaining each
occurrence as one parallel member. -/
def networkPattern (processes : List Process) (namespaceName valueName : String) : Pattern :=
  .collection .hashBag (processes.map (fun process => encode process namespaceName valueName)) none

theorem atom_restrictionFree {process : Process} (atom : Atom process) :
    RestrictionFree process := by
  cases process <;> simp only [Atom] at atom <;> exact atom

theorem components_flat {process : Process} (free : RestrictionFree process) :
    Flat (components process) := by
  induction process with
  | nil => intro member membership; simp [components] at membership
  | par left right leftIH rightIH =>
      intro member membership
      rcases List.mem_append.mp membership with fromLeft | fromRight
      · exact leftIH free.1 member fromLeft
      · exact rightIH free.2 member fromRight
  | input channel binder body =>
      intro member membership
      simpa [components] using (List.mem_singleton.mp membership ▸ free)
  | output channel datum =>
      intro member membership
      obtain rfl := List.mem_singleton.mp membership
      trivial
  | nu | replicate => exact False.elim free

theorem assemble_restrictionFree {processes : List Process} (flat : Flat processes) :
    RestrictionFree (assemble processes) := by
  induction processes with
  | nil => trivial
  | cons process processes ih =>
      exact ⟨atom_restrictionFree (flat process (by simp)),
        ih (fun member membership => flat member (by simp [membership]))⟩

theorem assemble_append (first second : List Process) :
    Nonempty (StructuralCongruenceRF (assemble (first ++ second))
      (.par (assemble first) (assemble second))) := by
  induction first with
  | nil => exact ⟨.symm _ _ (.par_nil_left _)⟩
  | cons first rest ih =>
      obtain ⟨related⟩ := ih
      exact ⟨.trans _ _ _ (.par_cong _ _ _ _ (.refl _) related)
        (.symm _ _ (.par_assoc _ _ _))⟩

theorem assemble_components (process : Process) :
    Nonempty (StructuralCongruenceRF (assemble (components process)) process) := by
  induction process with
  | nil => exact ⟨.refl _⟩
  | par left right leftIH rightIH =>
      obtain ⟨append⟩ := assemble_append (components left) (components right)
      obtain ⟨leftRelated⟩ := leftIH
      obtain ⟨rightRelated⟩ := rightIH
      exact ⟨.trans _ _ _ append (.par_cong _ _ _ _ leftRelated rightRelated)⟩
  | input | output | nu | replicate => exact ⟨.par_nil_right _⟩

theorem assemble_perm {first second : List Process} (permutation : first.Perm second) :
    Nonempty (StructuralCongruenceRF (assemble first) (assemble second)) := by
  induction permutation with
  | nil => exact ⟨.refl _⟩
  | cons first _ ih =>
      obtain ⟨related⟩ := ih
      exact ⟨.par_cong _ _ _ _ (.refl first) related⟩
  | swap first second rest =>
      exact ⟨.trans _ _ _ (.symm _ _ (.par_assoc _ _ _))
        (.trans _ _ _ (.par_cong _ _ _ _ (.par_comm _ _) (.refl _))
          (.par_assoc _ _ _))⟩
  | trans _ _ firstIH secondIH =>
      obtain ⟨firstRelated⟩ := firstIH
      obtain ⟨secondRelated⟩ := secondIH
      exact ⟨.trans _ _ _ firstRelated secondRelated⟩

private theorem atom_encode_not_bag {process : Process} (atom : Atom process)
    (namespaceName valueName : String) (elements : List Pattern) :
    encode process namespaceName valueName ≠ .collection .hashBag elements none := by
  cases process <;> simp [Atom] at atom
  all_goals simp [encode, rhoInput, rhoOutput]

/-- On actual communication components, list compilation is exactly the
existing compiler applied to their named parallel assembly. -/
theorem encode_assemble {processes : List Process} (flat : Flat processes)
    (namespaceName valueName : String) :
    encode (assemble processes) namespaceName valueName =
      networkPattern processes namespaceName valueName := by
  induction processes generalizing namespaceName with
  | nil => rfl
  | cons process processes ih =>
      have headAtom := flat process (by simp)
      have tailFlat : Flat processes := fun member membership => flat member (by simp [membership])
      change rhoPar (encode process (namespaceName ++ "_L") valueName)
        (encode (assemble processes) (namespaceName ++ "_R") valueName) = _
      rw [ih tailFlat]
      rw [encode_rf_ns_independent (atom_restrictionFree headAtom)
        (namespaceName ++ "_L") namespaceName valueName]
      have tailMap : processes.map (fun process => encode process (namespaceName ++ "_R") valueName) =
          processes.map (fun process => encode process namespaceName valueName) := by
        apply List.map_congr_left
        intro member membership
        exact encode_rf_ns_independent (atom_restrictionFree (tailFlat member membership)) _ _ _
      rw [networkPattern, tailMap]
      cases process <;> simp [Atom] at headAtom
      all_goals rfl

/-- All body substitutions permitted by the maintained compiler are safe for
every enabled pair in this supplied network. This is a syntactic variable
condition, independent of the target execution. -/
def Safe (processes : List Process) : Prop :=
  ∀ channel binder datum body,
    .input channel binder body ∈ processes →
    .output channel datum ∈ processes →
    binder ≠ datum ∧ BarendregtFor binder datum body

/-- A selected named communication, including the exact two consumed
occurrences and the newly unguarded components. -/
inductive NetworkStep : List Process → List Process → Prop where
  | comm {processes : List Process}
      (inputIndex : Nat) (inputBound : inputIndex < processes.length)
      (outputIndex : Nat) (outputBound : outputIndex < (processes.eraseIdx inputIndex).length)
      (channel binder datum : Name) (body : Process)
      (input : processes[inputIndex] = .input channel binder body)
      (output : (processes.eraseIdx inputIndex)[outputIndex] = .output channel datum) :
      NetworkStep processes
        (components (body.substitute binder datum) ++
          (processes.eraseIdx inputIndex).eraseIdx outputIndex)

theorem NetworkStep.flat {source target : List Process}
    (step : NetworkStep source target) (flat : Flat source) : Flat target := by
  cases step with
  | comm i hi j hj channel binder datum body input output =>
      have bodyFree : RestrictionFree body := by
        have := flat source[i] (List.getElem_mem hi)
        simpa [input, Atom] using this
      intro process membership
      rcases List.mem_append.mp membership with released | retained
      · exact components_flat (rf_substitute bodyFree binder datum) process released
      · exact flat process (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx retained))

/-- Occurrence-indexed communication is an actual named pi reduction. The
parallel rearrangements used to expose the two selected occurrences are
existing source equations; they do not modify either guarded body. -/
theorem NetworkStep.named {source target : List Process}
    (step : NetworkStep source target) (safe : Safe source) :
    ∃ reduction : ReducesRF (assemble source) (assemble target), CommSafe reduction := by
  cases step with
  | comm i hi j hj channel binder datum body input output =>
      let rest := (source.eraseIdx i).eraseIdx j
      have permutation :
          (.input channel binder body :: .output channel datum :: rest).Perm source := by
        have second := List.getElem_cons_eraseIdx_perm hj
        have first := List.getElem_cons_eraseIdx_perm hi
        have both := (second.cons source[i]).trans first
        simpa [input, output, rest] using both
      obtain ⟨rearranged⟩ := assemble_perm permutation.symm
      have exposed : StructuralCongruenceRF (assemble source)
          (.par (.par (.input channel binder body) (.output channel datum)) (assemble rest)) :=
        .trans _ _ _ rearranged (.symm _ _ (.par_assoc _ _ _))
      obtain ⟨targetAppend⟩ := assemble_append (components (body.substitute binder datum)) rest
      obtain ⟨targetComponents⟩ := assemble_components (body.substitute binder datum)
      have joined : StructuralCongruenceRF
          (assemble (components (body.substitute binder datum) ++ rest))
          (.par (body.substitute binder datum) (assemble rest)) :=
        .trans _ _ _ targetAppend (.par_cong _ _ _ _ targetComponents (.refl _))
      have commSafe := safe channel binder datum body
        (input ▸ List.getElem_mem hi)
        (output ▸ List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      exact ⟨.struct _ _ _ _ exposed
        (.par_left _ _ _ (.comm channel binder datum body)) (.symm _ _ joined), commSafe⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint
