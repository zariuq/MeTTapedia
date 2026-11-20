import Mettapedia.GSLT.Contracts.AddressedCommits
import Mettapedia.GSLT.Contracts.PaperRhoAdequacy

/-!
# Communication on name classes

The paper's subject test uses name equivalence, not the order of
processes or the byte identity of a spelling. Given faithful keys,
the same keys can be used for both matching and addressing the selected
input occurrences. Subject separation is sufficient for a diamond of
selected positive commits; it is not a statement about which candidates
a later computation can discover on those channels.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho.Ports

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (canonicalize)

def key (name : Name) : Pattern :=
  canonicalize rhoReflectivePresentation (PatternBoundary.encodeName name)

theorem key_eq_iff {x y : Name} : key x = key y ↔ NameEquivalence x y :=
  Adequacy.canonicalize_encodeName_eq_iff x y

def sameSubject (x y : Name) : Bool := decide (key x = key y)

theorem sameSubject_eq_true_iff {x y : Name} :
    sameSubject x y = true ↔ NameEquivalence x y :=
  decide_eq_true_iff.trans key_eq_iff

theorem comm_on_keys {offered waiting : Name} {payload body : Process}
    (offerScope : ScopedName 0 offered) (waitScope : ScopedName 0 waiting)
    (payloadScope : ScopedProcess 0 payload) (bodyScope : ScopedProcess 1 body)
    (matchKeys : sameSubject offered waiting = true) :
    Reduction (.par (.send offered payload) (.receive waiting body)) (substitute payload 0 body) :=
  .comm offerScope waitScope payloadScope bodyScope
    (sameSubject_eq_true_iff.mp matchKeys) (substitute_fits payload 0 body)

private theorem rightPar {before after : Process} (step : Reduction before after) (frame : Process) :
    Reduction (.par frame before) (.par frame after) :=
  .equiv (.swap _ _) (.par frame step) (.swap _ _)

/-- For two already exposed redexes the paper relation itself has the
diamond. No condition on their contracta is required; a contractum may
offer on the other subject, creating additional choices. -/
theorem parallel_diamond {p p' q q' : Process}
    (left : Reduction p p') (right : Reduction q q') :
    Reduction (.par p q) (.par p' q) ∧
    Reduction (.par p' q) (.par p' q') ∧
    Reduction (.par p q) (.par p q') ∧
    Reduction (.par p q') (.par p' q') :=
  ⟨.par q left, rightPar right p', rightPar right p, .par q' left⟩

def assemble (parts : List Process) : Process := parts.foldr Process.par .zero

theorem assemble_perm {parts reordered : List Process} (order : parts.Perm reordered) :
    Congruence (assemble parts) (assemble reordered) := by
  induction order with
  | nil => exact .refl _
  | cons p _ ih => exact .par (.refl p) ih
  | swap a b _ =>
      exact .trans (.symm (.assoc b a _)) (.trans (.par (.swap b a) (.refl _)) (.assoc a b _))
  | trans _ _ first second => exact .trans first second

/-- A parallel family of selected, separate redex pieces has an
interleaving in the original paper relation, with no hosting
translation in either endpoint. -/
theorem assemble_reductions {before after : List Process}
    (parts : List.Forall₂ Reduction before after) :
    Relation.ReflTransGen Reduction (assemble before) (assemble after) := by
  induction parts with
  | nil => exact .refl
  | @cons p p' earlier later step _ ih =>
      exact (Relation.ReflTransGen.single (Reduction.par (assemble earlier) step)).trans
        (Relation.ReflTransGen.lift (Process.par p') (fun _ _ reduction => rightPar reduction p')
          (assemble earlier) (assemble later) ih)

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Contracts.AddressedCommits (selected independent_of_positive)

/-- This specialization works on COMMs and on other positive receipts
with one subject class. Rho supplies the key, not the transaction
definition or the storage discipline. -/
theorem distinct_subjects_diamond {O Atom Key : Type*} [DecidableEq O]
    (addressKey : Name → Key) (faithful : ∀ {a b}, addressKey a = addressKey b ↔ NameEquivalence a b)
    (label : O → Atom) (subject : Atom → Name) {store : Finset O} {c d : Commit O Atom}
    {x y : Name}
    (left : Enabled label store c) (right : Enabled label store d)
    (positiveLeft : c.Positive) (positiveRight : d.Positive)
    (onX : ∀ o ∈ c.uses, NameEquivalence (subject (label o)) x)
    (onY : ∀ o ∈ d.uses, NameEquivalence (subject (label o)) y)
    (different : ¬ NameEquivalence x y) (fresh : Disjoint c.made d.made) :
    Enabled label (fire store c) d ∧ Enabled label (fire store d) c ∧
      fire (fire store c) d = fire (fire store d) c := by
  have locations : Disjoint (selected label (addressKey ∘ subject) c)
      (selected label (addressKey ∘ subject) d) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨o, hc, xKey⟩ ⟨p, hd, yKey⟩
    apply different
    apply faithful.mp
    exact (faithful.mpr (onX o hc)).symm.trans
      (xKey.trans (yKey.symm.trans (faithful.mpr (onY p hd))))
  have independent := independent_of_positive label (addressKey ∘ subject)
    positiveLeft positiveRight locations fresh
  obtain ⟨thenRight, thenLeft⟩ := (independent_iff_both_orders left right).mp independent
  exact ⟨thenRight, thenLeft, fire_comm left right⟩

namespace Controls

open Separation (base wrapped)

/-- The raw spellings differ, but they are a single port for both
communication and conflict detection. -/
theorem alias_is_the_same_port : sameSubject base wrapped = true ∧ base ≠ wrapped := by
  refine ⟨sameSubject_eq_true_iff.mpr ?_, ?_⟩
  · exact NameEquivalence.symm (.quote_drop _)
  · intro same
    have impossible : Process.zero = .drop base := Name.quote.inj same
    cases impossible

end Controls

#print axioms key_eq_iff
#print axioms comm_on_keys
#print axioms parallel_diamond
#print axioms assemble_perm
#print axioms assemble_reductions
#print axioms distinct_subjects_diamond
#print axioms Controls.alias_is_the_same_port

end Mettapedia.GSLT.Contracts.PaperRho.Ports
