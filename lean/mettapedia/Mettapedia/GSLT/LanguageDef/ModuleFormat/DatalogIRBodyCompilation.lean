import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRFiringReading

/-! Clause compilation retains every positive atom and guard. The ordered
body is only a permutation separating binding queries from input guards. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BodyCompilation

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

theorem compiled_body (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) :
    clause.RangeRestricted ∧ ∃ premises,
      (Join.orderedBody clause).zipIdx.mapM (fun entry => Join.bodyPremise? pools entry.2 entry.1) = some premises ∧
      rule.premises = premises.map Query.lowerPremise := by
  obtain ⟨original,originalCompiled,rfl⟩ := Option.map_eq_some_iff.mp compiled
  cases safe : clause.checkRangeRestriction with
  | false => simp [Join.compileClause?,safe] at originalCompiled
  | true =>
    refine ⟨(Clause.checkRangeRestriction_iff clause).mp safe,?_⟩
    simp only [Join.compileClause?,safe,Bool.not_true,Bool.false_eq_true,if_false] at originalCompiled
    change ((Join.atom? pools clause.body.length clause.head).bind fun right =>
      ((Join.orderedBody clause).zipIdx.mapM fun entry => Join.bodyPremise? pools entry.2 entry.1).bind fun premises =>
        some ({
          name := "datalog-clause:" ++ toString ordinal
          typeContext := Join.variableContext pools clause
          premises := premises
          left := .apply "Infer" [Join.poolPattern (Join.relationSlots pools),
            Join.poolPattern (Join.literalSlots pools),.fvar "facts"]
          right := right } : RewriteRule)) = some original at originalCompiled
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at originalCompiled
    obtain ⟨_,_,premises,body,rfl⟩ := originalCompiled
    exact ⟨premises,body,rfl⟩

theorem ordered_atom (clause : Clause) (atom : Mettapedia.Languages.Datalog.Atom) :
    Mettapedia.Languages.Datalog.Premise.atom atom ∈ Join.orderedBody clause ↔ atom ∈ clause.positiveAtoms := by
  simp only [Join.orderedBody,List.mem_append,List.mem_filter,and_true, Bool.false_eq_true,
    and_false,or_false,Clause.positiveAtoms,List.mem_filterMap]
  constructor
  · intro member
    exact ⟨.atom atom,member,rfl⟩
  · rintro ⟨premise,member,selected⟩
    cases premise with
    | atom actual => cases Option.some.inj selected; exact member
    | comparison _ => cases selected

theorem ordered_guard (clause : Clause) (comparison : Comparison) :
    Mettapedia.Languages.Datalog.Premise.comparison comparison ∈ Join.orderedBody clause ↔
      comparison ∈ Comparisons.guards clause := by
  simp only [Join.orderedBody,List.mem_append,List.mem_filter,and_true, Bool.false_eq_true,
    and_false,false_or,Comparisons.guards,List.mem_filterMap]
  constructor
  · intro member
    exact ⟨.comparison comparison,member,rfl⟩
  · rintro ⟨premise,member,selected⟩
    cases premise with
    | atom _ => cases selected
    | comparison actual => cases Option.some.inj selected; exact member

private theorem split_body (body : List Mettapedia.Languages.Datalog.Premise) :
    body.filter (fun premise => match premise with | .atom _ => true | _ => false) =
      (body.filterMap fun premise => match premise with | .atom atom => some atom | _ => none).map Mettapedia.Languages.Datalog.Premise.atom ∧
    body.filter (fun premise => match premise with | .comparison _ => true | _ => false) =
      (body.filterMap fun premise => match premise with | .comparison comparison => some comparison | _ => none).map Mettapedia.Languages.Datalog.Premise.comparison := by
  induction body with
  | nil => exact ⟨rfl,rfl⟩
  | cons premise body ih => cases premise <;> simp [ih.1,ih.2]

theorem ordered_body (clause : Clause) : Join.orderedBody clause =
    clause.positiveAtoms.map Mettapedia.Languages.Datalog.Premise.atom ++
      (Comparisons.guards clause).map Mettapedia.Languages.Datalog.Premise.comparison := by
  have split := split_body clause.body
  exact congrArg₂ List.append split.1 split.2

theorem atom_premise (pools : Join.Pools) (position : Nat) (atom : Mettapedia.Languages.Datalog.Atom)
    (premise : Syntax.Premise) (compiled : Join.bodyPremise? pools position (.atom atom) = some premise) :
    ∃ code, Join.atom? pools position atom = some code ∧
      Query.lowerPremise premise = .relationQuery Query.factRelation [code] := by
  change ((Join.atom? pools position atom).bind fun code =>
    some (.congruence (.apply "LookupFact" [.fvar "facts"]) code)) = some premise at compiled
  obtain ⟨code,formed,same⟩ := Option.bind_eq_some_iff.mp compiled
  cases Option.some.inj same
  exact ⟨code,formed,rfl⟩

theorem guard_premise (pools : Join.Pools) (position : Nat) (comparison : Comparison)
    (premise : Syntax.Premise) (compiled : Join.bodyPremise? pools position (.comparison comparison) = some premise) :
    ∃ left right, Join.argument? pools position 0 comparison.left = some left ∧
      Join.argument? pools position 1 comparison.right = some right ∧
      Query.lowerPremise premise = .relationQuery (Join.comparisonName comparison.operator) [left,right] := by
  change ((Join.argument? pools position 0 comparison.left).bind fun left =>
    (Join.argument? pools position 1 comparison.right).bind fun right =>
      some (.relationQuery (Join.comparisonName comparison.operator) [left,right])) = some premise at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨left,leftCode,right,rightCode,rfl⟩ := compiled
  exact ⟨left,right,leftCode,rightCode,rfl⟩

#print axioms compiled_body
#print axioms ordered_atom
#print axioms ordered_guard
#print axioms ordered_body
#print axioms atom_premise
#print axioms guard_premise

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BodyCompilation
