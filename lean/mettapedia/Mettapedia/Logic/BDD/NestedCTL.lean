import Mettapedia.Logic.BDD.SymbolicCTL
import Mettapedia.Logic.BDD.BoundedFixedPoints
import Mettapedia.Logic.CTLFormula

/-!
# Total symbolic compilation of nested existential CTL

Every inner EU/EG is completed by the proved finite-state budget before its
diagram is used by a surrounding formula. Correctness is equality with the
independent nested path semantics. Labels and valid-state domains are retained
through negation and temporal operators. The relation's deadlock policy is
explicit; the compiler never inserts a successor implicitly.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.NestedCTL

open StatePredicates StateTransducer
open Mettapedia.Logic.CTLFormula

variable {Label : Type} {n : Nat} {domain : Diagram n}

theorem denote_conj (left right : Diagram n) : denote (conj left right) = denote left ∩ denote right := by
  ext state
  simp [denote, conj, BDD.satSet, apply_eval]

theorem denote_disj (left right : Diagram n) : denote (disj left right) = denote left ∪ denote right := by
  ext state
  simp [denote, disj, BDD.satSet, apply_eval]

theorem denote_complement (domain body : Diagram n) :
    denote (complement domain body) = denote domain \ denote body := by
  ext state
  simp [denote, complement, conj, neg, BDD.satSet, apply_eval, bddNot_eval]

def compile (program : Certified n domain) (atoms : Label → Diagram n) : Formula Label → Diagram n
  | .atom label => within domain (atoms label)
  | .truth => domain
  | .neg body => complement domain (compile program atoms body)
  | .conj left right => conj (compile program atoms left) (compile program atoms right)
  | .disj left right => disj (compile program atoms left) (compile program atoms right)
  | .ex body => pre domain program.rules (compile program atoms body)
  | .eu holds goal => BoundedFixedPoints.least
      (SymbolicCTL.untilOp program (compile program atoms holds) (compile program atoms goal))
  | .eg body => BoundedFixedPoints.greatest (SymbolicCTL.globallyOp program (compile program atoms body))

theorem compile_exact (program : Certified n domain) (atoms : Label → Diagram n) (formula : Formula Label) :
    denote (compile program atoms formula) =
      meaning (denote domain) (Relation domain program.rules) (fun label => denote (atoms label)) formula := by
  induction formula with
  | atom label => exact denote_conj domain (atoms label)
  | truth => rfl
  | neg body ih => simp only [compile, meaning, denote_complement, ih]
  | conj left right ihl ihr => simp only [compile, meaning, denote_conj, ihl, ihr]
  | disj left right ihl ihr => simp only [compile, meaning, denote_disj, ihl, ihr]
  | ex body ih =>
      rw [compile, SymbolicCTL.pre_denote, ih]
      apply Set.Subset.antisymm
      · rintro state ⟨next, edge, held⟩
        exact ⟨edge.1, next, edge, held⟩
      · exact Set.inter_subset_right
  | eu holds goal ihl ihr =>
      rw [compile, BoundedFixedPoints.least_denote]
      change (CTLFixedPoints.untilOperator (Relation domain program.rules)
        (denote (within domain (compile program atoms holds)))
        (denote (within domain (compile program atoms goal)))).lfp = _
      simp only [within, denote_conj, ihl, ihr,
        Set.inter_eq_right.mpr (meaning_within (denote domain) (Relation domain program.rules)
          (fun label => denote (atoms label)) holds),
        Set.inter_eq_right.mpr (meaning_within (denote domain) (Relation domain program.rules)
          (fun label => denote (atoms label)) goal)]
      ext state
      exact (CTLFixedPoints.until_iff_lfp _ _ _ state).symm
  | eg body ih =>
      rw [compile, BoundedFixedPoints.greatest_denote]
      change (CTLFixedPoints.globallyOperator (Relation domain program.rules)
        (denote (within domain (compile program atoms body)))).gfp = _
      rw [within, denote_conj, ih,
        Set.inter_eq_right.mpr (meaning_within (denote domain) (Relation domain program.rules)
          (fun label => denote (atoms label)) body)]
      ext state
      exact (CTLFixedPoints.globally_iff_gfp _ _ state).symm

theorem compile_within (program : Certified n domain) (atoms : Label → Diagram n) (formula : Formula Label) :
    denote (compile program atoms formula) ⊆ denote domain := by
  rw [compile_exact]
  exact meaning_within _ _ _ _

theorem unrelated_label_changes (program : Certified n domain)
    (first second : Label → Diagram n) (formula : Formula Label)
    (agree : ∀ label ∈ formula.labels, equivalent (first label) (second label) = true) :
    equivalent (compile program first formula) (compile program second formula) = true := by
  apply (equivalent_denote _ _).mpr
  rw [compile_exact, compile_exact]
  exact meaning_agrees _ _ _ _ formula (fun label present => (equivalent_denote _ _).mp (agree label present))

theorem reassociated_conjunction (program : Certified n domain) (atoms : Label → Diagram n)
    (a b c : Formula Label) :
    equivalent (compile program atoms (.conj (.conj a b) c))
      (compile program atoms (.conj a (.conj b c))) = true := by
  apply (equivalent_denote _ _).mpr
  rw [compile_exact, compile_exact]
  exact boolean_reassociation _ _ _ _ _ _

theorem double_negation_preserved (program : Certified n domain) (atoms : Label → Diagram n)
    (formula : Formula Label) : equivalent (compile program atoms (.neg (.neg formula)))
      (compile program atoms formula) = true := by
  apply (equivalent_denote _ _).mpr
  rw [compile_exact, compile_exact]
  exact double_negation _ _ _ _

end Mettapedia.Logic.BDDCore.NestedCTL
