import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidence

/-!
# Cut-independent evidence and traces up to fresh-name renaming

Evidence in a firing history has two separate invariance obligations.

First, an observation descends to the thin firing alphabet exactly when it is
constant on every fibre of the forgetful map.  A solver witness for the whole
ambient store generally fails this test; a firing-local witness may pass it.

Second, independent firings can allocate the same fresh identities in a
different order.  Rich trace comparison therefore combines the existing thin
trace relation with one global renaming of the rich evidence word.  A
commutative account is invariant under that comparison when its site value is
renaming-invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidence

universe uRich uBase uValue uRename uM

variable {Rich : Type uRich} {Base : Type uBase} {Value : Type uValue}

/-- An observation is cut-independent relative to the chosen thin firing
when equal thin firings force equal observations. -/
def FiberStable (forget : Rich → Base) (observe : Rich → Value) : Prop :=
  ∀ first second, forget first = forget second → observe first = observe second

/-- The observation is literally a function of the thin firing. -/
def FactorsThrough (forget : Rich → Base) (observe : Rich → Value) : Prop :=
  ∃ thin : Base → Value, ∀ rich, observe rich = thin (forget rich)

theorem FactorsThrough.fiberStable {forget : Rich → Base} {observe : Rich → Value}
    (factors : FactorsThrough forget observe) : FiberStable forget observe := by
  obtain ⟨thin, factor⟩ := factors
  intro first second same
  rw [factor first, factor second, same]

/-- On a surjective projection, fibre stability is also sufficient for a
thin observation. -/
theorem FiberStable.factorsThrough {forget : Rich → Base} {observe : Rich → Value}
    (onto : Function.Surjective forget) (stable : FiberStable forget observe) :
    FactorsThrough forget observe := by
  classical
  choose pick rightInverse using onto
  refine ⟨fun base => observe (pick base), fun rich => ?_⟩
  exact stable rich (pick (forget rich)) (rightInverse (forget rich)).symm

variable {Renaming : Type uRename} [Group Renaming] [MulAction Renaming Rich]

/-- Fresh-name transport does not change the underlying thin firing. -/
def ForgetEquivariant (forget : Rich → Base) : Prop :=
  ∀ (change : Renaming) firing, forget (change • firing) = forget firing

/-- A site observation ignores a consistent renaming of fresh identities. -/
def RenameInvariant (observe : Rich → Value) : Prop :=
  ∀ (change : Renaming) firing, observe (change • firing) = observe firing

/-- Rich trace comparison: the thin words are trace-equivalent, and one
global fresh-name renaming makes the rich firing occurrences a permutation.
The global map preserves aliasing between different events. -/
def TraceUpToRenaming (thinTrace : List Base → List Base → Prop)
    (forget : Rich → Base) (first second : List Rich) : Prop :=
  thinTrace (first.map forget) (second.map forget) ∧
    ∃ change : Renaming, (first.map fun firing => change • firing).Perm second

/-- The specialization to R22's static trace relation. -/
def staticTraceUpToRenaming {T S O : Type*} [DecidableEq O]
    (label : O → T)
    (forget : Rich → AnnotatedRuns.Firing T S O) (first second : List Rich) : Prop :=
  TraceUpToRenaming (Renaming := Renaming)
    (Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv
      (AnnotatedRuns.StaticIndependent label)) forget first second

theorem traceUpToRenaming_refl (thinTrace : List Base → List Base → Prop)
    (thinRefl : ∀ word, thinTrace word word) (forget : Rich → Base) :
    ∀ word, TraceUpToRenaming (Renaming := Renaming) thinTrace forget word word := by
  intro word
  exact ⟨thinRefl _, ⟨1, by simp⟩⟩

theorem traceUpToRenaming_symm (thinTrace : List Base → List Base → Prop)
    (thinSymm : ∀ first second, thinTrace first second → thinTrace second first)
    (forget : Rich → Base) :
    ∀ first second,
      TraceUpToRenaming (Renaming := Renaming) thinTrace forget first second →
      TraceUpToRenaming (Renaming := Renaming) thinTrace forget second first := by
  intro first second related
  obtain ⟨thin, change, rich⟩ := related
  refine ⟨thinSymm _ _ thin, ⟨change⁻¹, ?_⟩⟩
  have mapped := rich.symm.map (fun firing => change⁻¹ • firing)
  have cancelled :
      (first.map fun firing => change • firing).map
          (fun firing => change⁻¹ • firing) = first := by
    rw [List.map_map]
    change List.map (fun firing => change⁻¹ • change • firing) first = first
    calc
      List.map (fun firing => change⁻¹ • change • firing) first = List.map id first :=
        List.map_congr_left (fun firing present => inv_smul_smul change firing)
      _ = first := by simp
  rw [cancelled] at mapped
  exact mapped

theorem traceUpToRenaming_trans (thinTrace : List Base → List Base → Prop)
    (thinTrans : ∀ first second third, thinTrace first second → thinTrace second third →
      thinTrace first third) (forget : Rich → Base) :
    ∀ first second third,
      TraceUpToRenaming (Renaming := Renaming) thinTrace forget first second →
      TraceUpToRenaming (Renaming := Renaming) thinTrace forget second third →
      TraceUpToRenaming (Renaming := Renaming) thinTrace forget first third := by
  intro first second third left right
  obtain ⟨leftThin, leftChange, leftRich⟩ := left
  obtain ⟨rightThin, rightChange, rightRich⟩ := right
  refine ⟨thinTrans _ _ _ leftThin rightThin, ⟨rightChange * leftChange, ?_⟩⟩
  have mapped := leftRich.map (fun firing => rightChange • firing)
  have composed :
      (first.map fun firing => leftChange • firing).map
          (fun firing => rightChange • firing) =
        first.map (fun firing => (rightChange * leftChange) • firing) := by
    simp [List.map_map, mul_smul]
  rw [composed] at mapped
  exact mapped.trans rightRich

/-- Rich equivalence always projects to the declared thin trace relation. -/
theorem TraceUpToRenaming.thin {thinTrace : List Base → List Base → Prop}
    {forget : Rich → Base} {first second : List Rich}
    (related : TraceUpToRenaming (Renaming := Renaming) thinTrace forget first second) :
    thinTrace (first.map forget) (second.map forget) :=
  related.1

/-- If forgetting commutes with fresh-name transport, rich equivalence also
preserves the bag of thin firing occurrences. -/
theorem TraceUpToRenaming.thin_perm {thinTrace : List Base → List Base → Prop}
    {forget : Rich → Base}
    (equivariant : @ForgetEquivariant Rich Base Renaming _ _ forget)
    {first second : List Rich}
    (related : TraceUpToRenaming (Renaming := Renaming) thinTrace forget first second) :
    (first.map forget).Perm (second.map forget) := by
  obtain ⟨change, rich⟩ := related.2
  have mapped := rich.map forget
  have unchanged :
      (first.map fun firing => change • firing).map forget = first.map forget := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro firing present
    exact equivariant change firing
  rw [unchanged] at mapped
  exact mapped

def account [Monoid Value] (observe : Rich → Value) (word : List Rich) : Value :=
  (word.map observe).prod

/-- A commutative per-firing account descends through rich traces up to
renaming exactly under the expected site invariance. -/
theorem account_eq_of_traceUpToRenaming {M : Type uM} [CommMonoid M]
    {thinTrace : List Base → List Base → Prop} {forget : Rich → Base}
    (observe : Rich → M)
    (invariant : @RenameInvariant Rich M Renaming _ _ observe)
    {first second : List Rich}
    (related : TraceUpToRenaming (Renaming := Renaming) thinTrace forget first second) :
    account observe first = account observe second := by
  obtain ⟨change, rich⟩ := related.2
  have mapped := rich.map observe
  have unchanged : (first.map (fun firing => change • firing)).map observe = first.map observe := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro firing present
    exact invariant change firing
  unfold account
  rw [← unchanged]
  exact mapped.prod_eq

#print axioms FiberStable.factorsThrough
#print axioms traceUpToRenaming_symm
#print axioms traceUpToRenaming_trans
#print axioms account_eq_of_traceUpToRenaming

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidence
