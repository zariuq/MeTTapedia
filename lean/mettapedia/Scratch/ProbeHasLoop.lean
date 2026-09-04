import Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

namespace Metta

theorem probe_hasLoop_singleton_eq_of_ne (x y : VarName) (hne : x ≠ y) :
    Bindings.hasLoop [BindingRel.eq x y] = false := by
  simp [Bindings.hasLoop, Bindings.vars, Atom.vars, List.eraseDups_cons,
    Bindings.resolveAtomAux, Bindings.resolutionFuel,
    Bindings.eqRepresentative, Bindings.eqClassOrdered,
    Bindings.classValues, Bindings.lookupVal,
    Bindings.eqVarsInOrder, Bindings.eqClass, Bindings.eqClassAux,
    Bindings.eqStep, hne, Ne.symm hne]

end Metta

private def probeBindings : Metta.Bindings :=
  [Metta.BindingRel.eq "a" "b",
    Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])]

#eval Metta.Bindings.vars probeBindings
#eval Metta.Bindings.eqClassOrdered probeBindings "p"
#eval Metta.Bindings.classValues probeBindings "p"
#eval Metta.Bindings.eqClassOrdered probeBindings "a"
#eval Metta.Bindings.classValues probeBindings "a"
#eval Metta.Bindings.resolutionFuel probeBindings (.var "p")
#eval Metta.Bindings.resolveAtomAux probeBindings
  (Metta.Bindings.resolutionFuel probeBindings (.var "p")) [] (.var "p")
#eval Metta.Bindings.resolveAtomAux probeBindings
  (Metta.Bindings.resolutionFuel probeBindings (.var "a")) [] (.var "a")
#eval Metta.Bindings.resolveAtomAux probeBindings
  (Metta.Bindings.resolutionFuel probeBindings (.var "b")) [] (.var "b")

private def traceBindings : Metta.Bindings :=
  [Metta.BindingRel.eq "qa" "qb",
    Metta.BindingRel.val "qa" (.sym "k"),
    Metta.BindingRel.val "qb" (.sym "k"),
    Metta.BindingRel.val "rp" (.expr [.sym "f", .var "qa"])]

private def forkBindings : Metta.Bindings :=
  [Metta.BindingRel.val "y" (.sym "k"),
    Metta.BindingRel.eq "z" "y", Metta.BindingRel.eq "x" "z",
    Metta.BindingRel.val "p"
      (.expr [.sym "f", .var "x", .var "x", .var "y", .var "z"])]

#eval Metta.Bindings.vars traceBindings
#eval (Metta.Bindings.vars traceBindings).map fun x =>
  (x, Metta.Bindings.resolveAtomAux traceBindings
    (Metta.Bindings.resolutionFuel traceBindings (.var x)) [] (.var x))
#eval Metta.Bindings.vars forkBindings
#eval (Metta.Bindings.vars forkBindings).map fun x =>
  (x, Metta.Bindings.resolveAtomAux forkBindings
    (Metta.Bindings.resolutionFuel forkBindings (.var x)) [] (.var x))
