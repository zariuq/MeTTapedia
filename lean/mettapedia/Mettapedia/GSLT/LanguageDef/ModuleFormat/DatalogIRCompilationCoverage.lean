import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRProgram

/-! Compilation succeeds whenever the finite vocabulary contains the source
names and literals. The executable compiler is unchanged; coverage is proved
for its actual lookups and ordered premise compilation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

theorem mapM_exists {α β : Type} (read : α → Option β) (values : List α)
    (total : ∀ value ∈ values, ∃ result, read value = some result) :
    ∃ results, values.mapM read = some results := by
  induction values with
  | nil => exact ⟨[],rfl⟩
  | cons value rest ih =>
      obtain ⟨result,head⟩ := total value (by simp)
      obtain ⟨results,tail⟩ := ih (fun value member => total value (by simp [member]))
      exact ⟨result :: results, by simp [head,tail]⟩

theorem relation_exists (pools : Pools) (name : QualifiedName) (member : name ∈ pools.relations) :
    ∃ code, relation? pools name = some code := by
  obtain ⟨index,found⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr member)
  exact ⟨.fvar (relationSlot index),by simp [relation?,found]⟩

theorem argument_exists (pools : Pools) (argument : Argument) (site position : Nat)
    (covered : ∀ value, argument = .literal value → value ∈ pools.literals) :
    ∃ code, argument? pools site position argument = some code := by
  cases argument with
  | var name => exact ⟨_,rfl⟩
  | anonymous => exact ⟨_,rfl⟩
  | literal value =>
      obtain ⟨index,found⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr (covered value rfl))
      exact ⟨.fvar (literalSlot index),by simp [argument?,literal?,found]⟩

theorem atom_exists (pools : Pools) (atom : Mettapedia.Languages.Datalog.Atom) (site : Nat)
    (relation : atom.relation ∈ pools.relations)
    (literals : ∀ value, Argument.literal value ∈ atom.arguments → value ∈ pools.literals) :
    ∃ code, atom? pools site atom = some code := by
  obtain ⟨name,nameRead⟩ := relation_exists pools atom.relation relation
  obtain ⟨arguments,argsRead⟩ := mapM_exists
    (fun entry : Argument × Nat => argument? pools site entry.2 entry.1) atom.arguments.zipIdx (by
      intro entry member
      apply argument_exists
      intro value same
      exact literals value (same ▸ List.fst_mem_of_mem_zipIdx member))
  exact ⟨.apply "GroundFact" [name,.apply "GroundTuple" [vector arguments]],by simp [atom?,nameRead,argsRead]⟩

def PremiseCovered (pools : Pools) : Mettapedia.Languages.Datalog.Premise → Prop
  | .atom atom => atom.relation ∈ pools.relations ∧
      ∀ value, Argument.literal value ∈ atom.arguments → value ∈ pools.literals
  | .comparison comparison =>
      (∀ value, comparison.left = .literal value → value ∈ pools.literals) ∧
      (∀ value, comparison.right = .literal value → value ∈ pools.literals)

theorem premise_exists (pools : Pools) (premise : Mettapedia.Languages.Datalog.Premise) (site : Nat)
    (covered : PremiseCovered pools premise) : ∃ code, bodyPremise? pools site premise = some code := by
  cases premise with
  | atom atom =>
      obtain ⟨code,read⟩ := atom_exists pools atom site covered.1 covered.2
      exact ⟨.congruence (.apply "LookupFact" [.fvar "facts"]) code,by simp [bodyPremise?,read]⟩
  | comparison comparison =>
      obtain ⟨left,leftRead⟩ := argument_exists pools comparison.left site 0 covered.1
      obtain ⟨right,rightRead⟩ := argument_exists pools comparison.right site 1 covered.2
      exact ⟨.relationQuery (comparisonName comparison.operator) [left,right],by simp [bodyPremise?,leftRead,rightRead]⟩

theorem clause_exists (pools : Pools) (ordinal : Nat) (clause : Clause)
    (restricted : clause.RangeRestricted)
    (relation : clause.head.relation ∈ pools.relations)
    (literals : ∀ value, Argument.literal value ∈ clause.head.arguments → value ∈ pools.literals)
    (body : ∀ premise ∈ clause.body, PremiseCovered pools premise) :
    ∃ rule, compileClause? pools ordinal clause = some rule := by
  obtain ⟨head,headRead⟩ := atom_exists pools clause.head clause.body.length relation literals
  obtain ⟨premises,premisesRead⟩ := mapM_exists
    (fun entry : Mettapedia.Languages.Datalog.Premise × Nat => bodyPremise? pools entry.2 entry.1)
    (orderedBody clause).zipIdx (by
      intro entry member
      apply premise_exists
      have present := List.fst_mem_of_mem_zipIdx member
      simp only [orderedBody, List.mem_append, List.mem_filter] at present
      exact body entry.1 (present.elim And.left And.left))
  refine ⟨{ name := "datalog-clause:" ++ toString ordinal
            typeContext := variableContext pools clause
            premises := premises
            left := .apply "Infer" [poolPattern (relationSlots pools),poolPattern (literalSlots pools),.fvar "facts"]
            right := head }, ?_⟩
  simp [compileClause?,(Clause.checkRangeRestriction_iff clause).mpr restricted,headRead,premisesRead]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join
