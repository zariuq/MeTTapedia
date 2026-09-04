import Mettapedia.Languages.MeTTa.HE.LeaTTaMatcherCongruence

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

private def nestedAliasProbe : Metta.Bindings :=
  [Metta.BindingRel.val "x" (.expr [.sym "f", .var "u"]),
   Metta.BindingRel.val "y" (.expr [.sym "f", .var "v"]),
   Metta.BindingRel.val "u" (.sym "a"),
   Metta.BindingRel.val "v" (.sym "a")]

#eval
  match Metta.Bindings.reconcileAll nestedAliasProbe
      [(.var "x", .var "y")] with
  | none => ("failed", [], [], none)
  | some sigma =>
      let rebuilt := Metta.Bindings.rebuildFromReconciliation
        (Metta.Bindings.addEqRaw nestedAliasProbe "x" "y")
        nestedAliasProbe [(.var "x", .var "y")] sigma
      ("succeeded", sigma, rebuilt,
        Metta.Bindings.unifyValues (Metta.Bindings.classValues rebuilt "x"))
#eval Metta.Bindings.addVarEquality nestedAliasProbe "x" "y"

/- The same semantic system with `u` grounded before the `y` value.  Repaired
reconciliation retains the compound collision's inner alias independently of
this operational ordering. -/
private def transientAliasProbe : Metta.Bindings :=
  [Metta.BindingRel.val "x" (.expr [.sym "f", .var "u"]),
   Metta.BindingRel.val "u" (.sym "a"),
   Metta.BindingRel.val "y" (.expr [.sym "f", .var "v"]),
   Metta.BindingRel.val "v" (.sym "a")]

private def transientAliasProbeHE : Bindings :=
  { assignments :=
      [("x", .expression [.symbol "f", .var "u"]),
       ("u", .symbol "a"),
       ("y", .expression [.symbol "f", .var "v"]),
       ("v", .symbol "a")]
    equalities := [] }

private def transientAliasRightHE : Bindings :=
  Bindings.empty.addEquality "x" "y"

private def transientAliasRightLea : Metta.Bindings :=
  [Metta.BindingRel.eq "y" "x"]

private def transientAliasProbeLeaOut : Metta.Bindings :=
  [Metta.BindingRel.eq "u" "v",
   Metta.BindingRel.eq "y" "x",
   Metta.BindingRel.val "v" (.sym "a"),
   Metta.BindingRel.val "y" (.expr [.sym "f", .var "v"]),
   Metta.BindingRel.val "u" (.sym "a"),
   Metta.BindingRel.val "x" (.expr [.sym "f", .var "u"])]

#eval toLeaTTaMatchBindingsFull transientAliasProbeHE
#eval toLeaTTaMatchBindingsFull transientAliasRightHE

#eval
  match Metta.Bindings.reconcileAll transientAliasProbe
      [(.var "x", .var "y")] with
  | none => ("failed", [], [], [])
  | some sigma =>
      let aliases := Metta.Bindings.reconciliationAliases
        transientAliasProbe [(.var "x", .var "y")] sigma
      let rebuilt := Metta.Bindings.rebuildFromReconciliation
        (Metta.Bindings.addEqRaw transientAliasProbe "x" "y")
        transientAliasProbe [(.var "x", .var "y")] sigma
      ("succeeded", sigma, aliases,
        Metta.Bindings.eqClass rebuilt "u")

#eval Metta.matchAtoms (.var "y") (.var "x")
#eval Metta.Bindings.merge transientAliasProbe
  [Metta.BindingRel.eq "y" "x"]
#eval (Metta.Bindings.merge transientAliasProbe
  [Metta.BindingRel.eq "y" "x"]).map
    (fun out => Metta.Bindings.eqClass out "u")

#eval matchAtoms (.var "x") (.var "y") 5
#eval mergeBindings transientAliasProbeHE transientAliasRightHE 30
#eval (mergeBindings transientAliasProbeHE transientAliasRightHE 30).map
  (fun out => out.eqClass "u")

#eval Metta.Bindings.classValues
  (Metta.Bindings.addEqRaw transientAliasProbe "y" "x") "y"
#eval Metta.Bindings.unifyValues
  (Metta.Bindings.classValues
    (Metta.Bindings.addEqRaw transientAliasProbe "y" "x") "y")
#eval Metta.Bindings.reconcileAll transientAliasProbe
  [(.var "y", .var "x")]
#eval
  let work := [(.var "y", .var "x")] ++
    Metta.Bindings.equations transientAliasProbe
  Metta.Unify.aliasTrace (Metta.Bindings.equationFuel work) work

private theorem transient_inner_match_connects
    {out : Bindings}
    (hmatch : DeclMatchSpec.MatchRel
      (.expression [.symbol "f", .var "u"])
      (.expression [.symbol "f", .var "v"]) out) :
    "v" ∈ out.eqClass "u" := by
  cases hmatch with
  | expr hlist =>
      cases hlist with
      | cons hsymbol hmergeSymbol htail =>
          cases htail with
          | cons hvariables hmergeVariables hnil =>
              cases hnil
              have hright : "v" ∈
                  (Bindings.empty.addEquality "u" "v").eqClass "u" := by
                rw [EqualityClosure.mem_eqClass_iff_reachable]
                exact (show
                    (EqualityClosure.edgeGraph
                      (Bindings.empty.addEquality "u" "v").equalities).Adj
                        "u" "v" by
                  rw [EqualityClosure.edgeGraph_adj_iff]
                  simp [Bindings.empty, Bindings.addEquality]).reachable
              have hvariablesOut : _ =
                  (Bindings.empty.addEquality "u" "v") :=
                DeclMatchSpec.matchRel_varVar_inv hvariables
              rw [hvariablesOut] at hmergeVariables
              exact mergeBindings_right_eqClass_mono
                hmergeVariables hright

private theorem transient_addEquality_connects
    {out : Bindings}
    (hadd : DeclMergeSpec.AddVarEqualityRel
      transientAliasProbeHE "x" "y" out) :
    "v" ∈ out.eqClass "u" := by
  have hclassValues :
      (transientAliasProbeHE.addEquality "x" "y").classValues "x" =
        [.expression [.symbol "f", .var "u"],
         .expression [.symbol "f", .var "v"]] := by
    decide
  cases hadd with
  | consistent hconsistent =>
      rw [hclassValues] at hconsistent
      simp [Bindings.valuesConsistent] at hconsistent
  | pairConflict hvalues hinconsistent hmatch hmerge =>
      rw [hclassValues] at hvalues
      rcases hvalues with ⟨rfl, rfl⟩
      have hmatchedClass := transient_inner_match_connects hmatch
      exact mergeRel_right_eqClass_mono hmerge hmatchedClass
  | classConflict hvalues hinconsistent hmatch hmerge =>
      rw [hclassValues] at hvalues
      simp at hvalues

private theorem transient_merge_connects
    {out : Bindings} {fuel : Nat}
    (hmerge : out ∈ mergeBindings
      transientAliasProbeHE transientAliasRightHE fuel) :
    "v" ∈ out.eqClass "u" := by
  have hrel : DeclMergeSpec.MergeRel transientAliasProbeHE
      ({ assignments := [], equalities := [("x", "y")] } : Bindings) out := by
    simpa [transientAliasRightHE, Bindings.empty,
      Bindings.addEquality] using
        DeclMergeSpec.mergeBindings_sound hmerge
  cases hrel with
  | mk hassignments hequalities =>
      cases hassignments
      cases hequalities with
      | cons hadd htail =>
          cases htail
          exact transient_addEquality_connects hadd

private theorem transient_left_congruence :
    LeaBindingCongruence transientAliasProbeHE transientAliasProbe := by
  apply LeaBindingCongruence.of_rel
  constructor
  · intro key value
    simp [transientAliasProbeHE, transientAliasProbe]
    aesop
  · intro first second
    simp [transientAliasProbeHE, transientAliasProbe]

private theorem transient_right_congruence :
    LeaBindingCongruence transientAliasRightHE transientAliasRightLea := by
  apply LeaBindingCongruence.of_rel
  constructor
  · intro key value
    simp [transientAliasRightHE, transientAliasRightLea,
      Bindings.empty, Bindings.addEquality]
  · intro first second
    simp [transientAliasRightHE,
      transientAliasRightLea, Bindings.empty, Bindings.addEquality]
    aesop

private theorem transient_lea_merge_eq :
    Metta.Bindings.merge transientAliasProbe transientAliasRightLea =
      [transientAliasProbeLeaOut] := by
  have hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw transientAliasProbe "y" "x") "y") =
      some [("u", .var "v")] := by
    simp [transientAliasProbe, Metta.Bindings.addEqRaw,
      Metta.Bindings.classValues, Metta.Bindings.eqClassOrdered,
      Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
      Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
      Metta.Bindings.lookupVal, Metta.Bindings.unifyValues,
      Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
      Metta.Unify.decomposeEq, Metta.Unify.decomposeList,
      Metta.Subst.occurs, Metta.Subst.apply, Metta.Subst.lookup,
      Metta.Subst.extend, Metta.Subst.erase, Metta.Atom.size]
  have hreconcile : Metta.Bindings.reconcileAll transientAliasProbe
      [(.var "y", .var "x")] =
      some [("v", .sym "a"),
        ("y", .expr [.sym "f", .var "v"]),
        ("u", .sym "a"),
        ("x", .expr [.sym "f", .var "u"])] := by
    simp [transientAliasProbe, Metta.Bindings.reconcileAll,
      Metta.Bindings.equations, Metta.Bindings.relationEquation,
      Metta.Bindings.equationFuel, Metta.Unify.unifyRounds,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
      Metta.Unify.decomposeList, Metta.Subst.occurs,
      Metta.Subst.apply, Metta.Subst.lookup, Metta.Subst.extend,
      Metta.Subst.erase, Metta.Atom.size]
  simp [transientAliasRightLea, Metta.Bindings.merge,
    Metta.Bindings.mergeOne, Metta.Bindings.addVarEquality]
  rw [hunify, hreconcile]
  simp [transientAliasProbe, transientAliasProbeLeaOut,
    Metta.Bindings.rebuildFromReconciliation,
    Metta.Bindings.rebuildFromSubst, Metta.Bindings.reconciliationAliases,
    Metta.Bindings.restoreAlias, Metta.Bindings.equations,
    Metta.Bindings.relationEquation, Metta.Bindings.equationFuel,
    Metta.Unify.aliasTrace, Metta.Unify.decomposeAll,
    Metta.Unify.decomposeEq, Metta.Unify.decomposeList,
    Metta.Unify.aliasConstraints, Metta.Subst.occurs,
    Metta.Subst.apply, Metta.Subst.lookup, Metta.Atom.size,
    Metta.Bindings.equalitySkeleton, Metta.Bindings.ofSubst,
    Metta.Bindings.addEqRaw, Metta.Bindings.eqClass,
    Metta.Bindings.eqClassAux, Metta.Bindings.eqStep]

/-- The formerly missing observable is present on both the HE merge and the
repaired LeaTTa result. -/
theorem transientAlias_repaired_innerAlias_agrees
    {heOut : Bindings} {fuel : Nat}
    (hmerge : heOut ∈ mergeBindings
      transientAliasProbeHE transientAliasRightHE fuel) :
    Metta.Bindings.merge transientAliasProbe transientAliasRightLea =
        [transientAliasProbeLeaOut] ∧
      "v" ∈ heOut.eqClass "u" ∧
        "v" ∈ Metta.Bindings.eqClass transientAliasProbeLeaOut "u" := by
  refine ⟨transient_lea_merge_eq, transient_merge_connects hmerge, ?_⟩
  set_option maxRecDepth 100000 in
    decide

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
