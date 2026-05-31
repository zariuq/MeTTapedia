import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination

/-!
# Semiring-Generic Belief Propagation Core

This module introduces the smallest useful abstract layer for belief propagation
on factor graphs:

* **message families** between variable and factor nodes,
* **neighbor bookkeeping** on the bipartite graph,
* **local update equations** for variable-to-factor and factor-to-variable messages,
* **belief extraction** from incoming messages.

The design is intentionally schedule-agnostic.  It captures the algebraic
equations common to the literature while leaving room for later extensions:

* Pearl-style synchronous/asynchronous updates,
* Kschischang-Frey-Loeliger sum-product on trees,
* max-product / Viterbi style instantiations,
* tropical / cost-semiring variants.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators

namespace MessagePassing

variable {V K : Type*} [DecidableEq V]

namespace FactorGraph

variable (fg : FactorGraph V K)

/-- Factor neighbors of a variable, enumerated as a finset. -/
noncomputable def variableNeighborsFinset [Fintype fg.factors] (v : V) : Finset fg.factors :=
  Finset.univ.filter (fun f => v ∈ fg.scope f)

/-- All factor neighbors of `v` except the designated target factor `f`. -/
noncomputable def otherFactorNeighbors
    [Fintype fg.factors] [DecidableEq fg.factors] (v : V) (f : fg.factors) :
    Finset fg.factors :=
  (variableNeighborsFinset fg v).erase f

lemma mem_variableNeighborsFinset_iff [Fintype fg.factors] (v : V) (f : fg.factors) :
    f ∈ variableNeighborsFinset fg v ↔ v ∈ fg.scope f := by
  classical
  simp [variableNeighborsFinset]

lemma mem_otherFactorNeighbors_iff
    [Fintype fg.factors] [DecidableEq fg.factors]
    (v : V) (f g : fg.factors) :
    g ∈ otherFactorNeighbors fg v f ↔ g ≠ f ∧ v ∈ fg.scope g := by
  classical
  simp [otherFactorNeighbors, variableNeighborsFinset]

lemma otherFactorNeighbors_eq_empty_of_variableNeighbors_eq_singleton
    [Fintype fg.factors] [DecidableEq fg.factors]
    (v : V) (f : fg.factors)
    (h : variableNeighborsFinset fg v = {f}) :
    otherFactorNeighbors fg v f = ∅ := by
  classical
  simp [otherFactorNeighbors, h]

end FactorGraph

/-- Variable-to-factor messages. The family is total over variable-factor pairs;
the update equations only inspect true neighbors. -/
abbrev VarToFactorMsg (fg : FactorGraph V K) : Type _ :=
  ∀ (v : V), fg.factors → fg.stateSpace v → K

/-- Factor-to-variable messages. -/
abbrev FactorToVarMsg (fg : FactorGraph V K) : Type _ :=
  ∀ (v : V), fg.factors → fg.stateSpace v → K

section Core

variable {fg : FactorGraph V K}

/-- Assignment on a singleton scope. -/
noncomputable def singletonAssign (v : V) (x_v : fg.stateSpace v) :
    VariableElimination.FactorGraph.Assign (fg := fg) ({v} : Finset V) :=
  fun u hu => by
    have huv : u = v := by simpa using hu
    subst huv
    exact x_v

/-- Assignment on an actual factor scope known to be the singleton `{v}`. -/
noncomputable def singletonScopeAssign
    (f : fg.factors) (v : V) (hscope : fg.scope f = {v}) (x_v : fg.stateSpace v) :
    ∀ u ∈ fg.scope f, fg.stateSpace u :=
  fun u hu => by
    have huv : u = v := by simpa [hscope] using hu
    subst huv
    exact x_v

/-- Canonical assignment on the "other variables" scope when that scope is empty. -/
noncomputable def emptyOtherScopeAssign
    (f : fg.factors) (v : V) (hEmpty : (fg.scope f).erase v = ∅) :
    VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v) := by
  simpa [hEmpty] using
    (VariableElimination.Factor.emptyAssign (fg := fg) :
      VariableElimination.FactorGraph.Assign (fg := fg) (∅ : Finset V))

/-- Assignment on a singleton "other scope". -/
noncomputable def singletonOtherScopeAssign
    (f : fg.factors) (v u : V) (hSingle : (fg.scope f).erase v = {u}) (x_u : fg.stateSpace u) :
    VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v) :=
  fun w hw => by
    have hwu : w = u := by
      simpa [hSingle] using hw
    subst hwu
    exact x_u

/-- An assignment on a singleton scope is equivalent to a value of that variable. -/
noncomputable def singletonOtherScopeEquiv
    (f : fg.factors) (v u : V) (hSingle : (fg.scope f).erase v = {u}) :
    VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v) ≃ fg.stateSpace u where
  toFun := fun x => x u (by simp [hSingle])
  invFun := singletonOtherScopeAssign (fg := fg) f v u hSingle
  left_inv := by
    intro x
    funext w hw
    have hwu : w = u := by
      simpa [hSingle] using hw
    subst hwu
    simp [singletonOtherScopeAssign]
  right_inv := by
    intro x_u
    simp [singletonOtherScopeAssign]

/-- Neutral initialization for variable-to-factor messages. -/
def unitVarToFactor [One K] : VarToFactorMsg fg :=
  fun _ _ _ => 1

/-- Neutral initialization for factor-to-variable messages. -/
def unitFactorToVar [One K] : FactorToVarMsg fg :=
  fun _ _ _ => 1

/-- Variable-to-factor update: product of all incoming factor-to-variable
messages except the target factor. -/
noncomputable def varToFactorUpdate
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K]
    (μ : FactorToVarMsg fg) (v : V) (f : fg.factors) (_hv : v ∈ fg.scope f) :
    fg.stateSpace v → K :=
  fun x =>
    Finset.prod ((FactorGraph.otherFactorNeighbors fg v f).attach) (fun g =>
      μ v g.1 x)

/-- Factor-to-variable update: sum over local assignments to the other variables
in the factor scope, multiplying the factor potential with incoming
variable-to-factor messages. -/
noncomputable def factorToVarUpdate
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)]
    (μ : VarToFactorMsg fg) (f : fg.factors) (v : V) (hv : v ∈ fg.scope f) :
    fg.stateSpace v → K :=
  let φ := VariableElimination.Factor.ofGraph (fg := fg) f
  fun x_v =>
    Finset.sum (Finset.univ :
      Finset (VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v))) (fun x =>
      let full := VariableElimination.Factor.extend (fg := fg) (φ := φ) v hv x x_v
      φ.potential full *
        Finset.prod (((fg.scope f).erase v).attach) (fun u =>
          μ u.1 f (x u.1 u.2)))

/-- Belief at a variable node: product of all incoming factor-to-variable
messages. -/
noncomputable def variableBelief
    [Fintype fg.factors] [CommMonoid K]
    (μ : FactorToVarMsg fg) (v : V) : fg.stateSpace v → K :=
  fun x =>
    Finset.prod ((FactorGraph.variableNeighborsFinset fg v).attach) (fun f =>
      μ v f.1 x)

/-- Belief at a factor node: local factor potential times all incoming
variable-to-factor messages. -/
noncomputable def factorBelief
    [CommMonoid K] (μ : VarToFactorMsg fg) (f : fg.factors) :
    VariableElimination.FactorGraph.Assign (fg := fg) (fg.scope f) → K :=
  fun x =>
    fg.potential f x *
      Finset.prod ((fg.scope f).attach) (fun v =>
        μ v.1 f (x v.1 v.2))

theorem varToFactorUpdate_eq_one_of_otherFactorNeighbors_eq_empty
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K]
    (μ : FactorToVarMsg fg) (v : V) (f : fg.factors) (hv : v ∈ fg.scope f)
    (h : FactorGraph.otherFactorNeighbors fg v f = ∅) :
    varToFactorUpdate (fg := fg) μ v f hv = fun _ => 1 := by
  funext x
  simp [varToFactorUpdate]
  have hattach : (FactorGraph.otherFactorNeighbors fg v f).attach = ∅ := by
    simp [h]
  rw [hattach]
  simp

theorem varToFactorUpdate_eq_one_of_variableNeighbors_eq_singleton
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K]
    (μ : FactorToVarMsg fg) (v : V) (f : fg.factors) (hv : v ∈ fg.scope f)
    (h : FactorGraph.variableNeighborsFinset fg v = {f}) :
    varToFactorUpdate (fg := fg) μ v f hv = fun _ => 1 := by
  apply varToFactorUpdate_eq_one_of_otherFactorNeighbors_eq_empty
  exact FactorGraph.otherFactorNeighbors_eq_empty_of_variableNeighbors_eq_singleton
    (fg := fg) v f h

theorem variableBelief_unitFactorToVar_eq_one
    [Fintype fg.factors] [CommMonoid K] (v : V) :
    variableBelief (fg := fg) (unitFactorToVar (fg := fg)) v = fun _ => 1 := by
  funext x
  simp [variableBelief, unitFactorToVar]

omit [DecidableEq V] in
theorem factorBelief_unitVarToFactor_eq_ofGraph
    [CommMonoid K] (f : fg.factors) :
    factorBelief (fg := fg) (unitVarToFactor (fg := fg)) f =
      (VariableElimination.Factor.ofGraph (fg := fg) f).potential := by
  funext x
  simp [factorBelief, unitVarToFactor, VariableElimination.Factor.ofGraph]

theorem factorToVarUpdate_eq_potential_of_otherScopeEmpty
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)]
    (μ : VarToFactorMsg fg) (f : fg.factors) (v : V) (hv : v ∈ fg.scope f)
    (hEmpty : (fg.scope f).erase v = ∅) :
    factorToVarUpdate (fg := fg) μ f v hv =
      fun x_v =>
        fg.potential f
          (VariableElimination.Factor.extend
            (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
            v hv
            (emptyOtherScopeAssign (fg := fg) f v hEmpty)
            x_v) := by
  classical
  funext x_v
  let x0 : VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v) :=
    emptyOtherScopeAssign (fg := fg) f v hEmpty
  have hEq
      (x : VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v)) :
      x = x0 := by
    funext u hu
    have : False := by
      simp [hEmpty] at hu
    exact this.elim
  have huniv :
      (Finset.univ :
        Finset (VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v))) =
        {x0} := by
    ext x
    simp [hEq x]
  have hAttach : ((fg.scope f).erase v).attach = ∅ := by
    ext u
    have : u.1 ∈ (fg.scope f).erase v := u.2
    have : False := by
      simp [hEmpty] at this
    simp [this]
  have hProd :
      Finset.prod (((fg.scope f).erase v).attach) (fun u =>
        μ u.1 f (x0 u.1 u.2)) = 1 := by
    rw [hAttach]
    simp
  calc
    factorToVarUpdate (fg := fg) μ f v hv x_v
        = ∑ x : VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v),
            (VariableElimination.Factor.ofGraph (fg := fg) f).potential
              (VariableElimination.Factor.extend
                (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
                v hv x x_v) *
              Finset.prod (((fg.scope f).erase v).attach) (fun u =>
                μ u.1 f (x u.1 u.2)) := by
            simp [factorToVarUpdate]
    _ = Finset.sum ({x0} :
          Finset (VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v))) (fun x =>
          (VariableElimination.Factor.ofGraph (fg := fg) f).potential
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
              v hv x x_v) *
            Finset.prod (((fg.scope f).erase v).attach) (fun u =>
              μ u.1 f (x u.1 u.2))) := by
            rw [huniv]
    _ = fg.potential f
          (VariableElimination.Factor.extend
            (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
            v hv x0 x_v) := by
          simp [hProd, VariableElimination.Factor.ofGraph]
    _ = fg.potential f
          (VariableElimination.Factor.extend
            (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
            v hv (emptyOtherScopeAssign (fg := fg) f v hEmpty)
            x_v) := by
          rfl

theorem factorToVarUpdate_eq_sum_of_otherScopeSingleton
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)]
    (μ : VarToFactorMsg fg) (f : fg.factors) (v u : V) (hv : v ∈ fg.scope f)
    (hSingle : (fg.scope f).erase v = {u}) :
    factorToVarUpdate (fg := fg) μ f v hv =
      fun x_v =>
        ∑ x_u : fg.stateSpace u,
          fg.potential f
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
              v hv
              (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
              x_v) *
            μ u f x_u := by
  classical
  funext x_v
  let F :
      VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v) → K :=
    fun x =>
      (VariableElimination.Factor.ofGraph (fg := fg) f).potential
        (VariableElimination.Factor.extend
          (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
          v hv x x_v) *
        Finset.prod (((fg.scope f).erase v).attach) (fun w =>
          μ w.1 f (x w.1 w.2))
  have hEquiv :
      (∑ x : VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v), F x) =
        ∑ x_u : fg.stateSpace u,
          F (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u) := by
    refine Fintype.sum_equiv
      (singletonOtherScopeEquiv (fg := fg) f v u hSingle)
      F
      (fun x_u => F (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)) ?_
    intro x
    have hx :
        singletonOtherScopeAssign (fg := fg) f v u hSingle
          ((singletonOtherScopeEquiv (fg := fg) f v u hSingle) x) = x :=
      (singletonOtherScopeEquiv (fg := fg) f v u hSingle).left_inv x
    simpa [singletonOtherScopeEquiv] using congrArg F hx.symm
  calc
    factorToVarUpdate (fg := fg) μ f v hv x_v
        = ∑ x : VariableElimination.FactorGraph.Assign (fg := fg) ((fg.scope f).erase v), F x := by
            simp [factorToVarUpdate, F]
    _ = ∑ x_u : fg.stateSpace u,
          F (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u) := hEquiv
    _ = ∑ x_u : fg.stateSpace u,
          fg.potential f
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
              v hv
              (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
              x_v) *
            μ u f x_u := by
          apply Fintype.sum_congr
          intro x_u
          have hu_mem : u ∈ (fg.scope f).erase v := by
            simp [hSingle]
          have hAttach :
              (((fg.scope f).erase v).attach :
                Finset { w : V // w ∈ (fg.scope f).erase v }) = {⟨u, hu_mem⟩} := by
            ext w
            constructor
            · intro _
              simp only [Finset.mem_singleton]
              apply Subtype.ext
              simpa [hSingle] using w.property
            · intro hw
              simp
          have hProd :
              Finset.prod (((fg.scope f).erase v).attach) (fun w =>
                μ w.1 f
                  ((singletonOtherScopeAssign (fg := fg) f v u hSingle x_u) w.1 w.2)) =
                μ u f x_u := by
            rw [hAttach]
            simp [singletonOtherScopeAssign]
          have hMul :
              fg.potential f
                  (VariableElimination.Factor.extend
                    (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
                    v hv
                    (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
                    x_v) *
                Finset.prod (((fg.scope f).erase v).attach) (fun w =>
                  μ w.1 f
                    ((singletonOtherScopeAssign (fg := fg) f v u hSingle x_u) w.1 w.2)) =
              fg.potential f
                  (VariableElimination.Factor.extend
                    (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
                    v hv
                    (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
                    x_v) *
                μ u f x_u := by
            exact congrArg
              (fun z =>
                fg.potential f
                  (VariableElimination.Factor.extend
                    (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
                    v hv
                    (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
                    x_v) * z)
              hProd
          simpa [F, singletonOtherScopeAssign, VariableElimination.Factor.ofGraph] using hMul

end Core

end MessagePassing

end Mettapedia.ProbabilityTheory.BayesianNetworks
