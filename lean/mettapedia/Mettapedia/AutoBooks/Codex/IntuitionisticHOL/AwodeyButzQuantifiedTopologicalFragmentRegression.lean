import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzQuantifiedTopologicalFragment

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL
open SimpleTopologicalInterpretation

namespace AwodeyButzQuantifiedTopologicalFragmentRegression

inductive DemoBase where
  | atom
  deriving DecidableEq, Repr

inductive DemoConst : Ty DemoBase → Type where
  | truth : DemoConst .prop
  | falsehood : DemoConst .prop
  | atomWitness : DemoConst (.base .atom)

/-- A two-point proposition object over `Bool`, with fibers `{false, true}` over each base point. -/
def boolClassifier : EtaleSpace Bool where
  Carrier := Bool × Bool
  carrierTopologicalSpace := inferInstance
  proj := Prod.fst
  isLocalHomeomorph_proj := by
    apply IsLocalHomeomorph.mk
    intro xb
    rcases xb with ⟨x, b⟩
    use
      { toFun := Prod.fst
        invFun := fun y => (y, b)
        source := Set.univ ×ˢ ({b} : Set Bool)
        target := Set.univ
        map_source' := fun _ _ => Set.mem_univ _
        map_target' := fun _ _ => ⟨Set.mem_univ _, Set.mem_singleton b⟩
        left_inv' := fun y hy => by
          rcases y with ⟨y, b'⟩
          simp at hy
          simp [hy]
        right_inv' := fun _ _ => rfl
        open_source := isOpen_univ.prod (isOpen_discrete _)
        open_target := isOpen_univ
        continuousOn_toFun := continuous_fst.continuousOn
        continuousOn_invFun := by
          apply Continuous.continuousOn
          fun_prop }
    exact ⟨⟨Set.mem_univ x, Set.mem_singleton b⟩, fun _ _ => rfl⟩

def trueSection : boolClassifier.GlobalSection where
  toContinuousMap :=
    { toFun := fun x => (x, true)
      continuous_toFun := continuous_id.prodMk continuous_const }
  proj_comp := by
    funext x
    rfl

def falseSection : boolClassifier.GlobalSection where
  toContinuousMap :=
    { toFun := fun x => (x, false)
      continuous_toFun := continuous_id.prodMk continuous_const }
  proj_comp := by
    funext x
    rfl

def demoInterp : SimpleTopologicalInterpretation DemoBase DemoConst Bool where
  propSpace := boolClassifier
  baseSpace := fun _ => EtaleSpace.refl Bool
  constProp
    | .truth => trueSection
    | .falsehood => falseSection
  constBase := by
    intro b c
    cases c
    exact EtaleSpace.GlobalSection.terminal Bool

def demoPropInterp : SimplePropositionalInterpretation DemoBase DemoConst Bool where
  toSimple := demoInterp
  topPred := CtxTerm.const demoInterp [] .prop DemoConst.truth
  botPred := CtxTerm.const demoInterp [] .prop DemoConst.falsehood
  andPred := CtxTerm.var demoInterp
    (SimpleVar.vz : SimpleVar DemoBase [.prop, .prop] .prop)
  orPred := CtxTerm.var demoInterp
    (SimpleVar.vs (SimpleVar.vz : SimpleVar DemoBase [.prop] .prop))
  impPred := CtxTerm.const demoInterp [.prop, .prop] .prop DemoConst.truth

def demoQuantInterp : SimpleQuantifiedInterpretation DemoBase DemoConst Bool where
  toPropositional := demoPropInterp
  allPred := fun {_ _} _ => demoPropInterp.top _
  exPred := fun {_ _} _ => demoPropInterp.bot _
  all_reindex := by
    intro τ Γ Δ p σ
    simp
  ex_reindex := by
    intro τ Γ Δ p σ
    simp

def forallTop : SimpleQuantifiedFormula DemoBase DemoConst [] :=
  .all .prop .top

def existsTop : SimpleQuantifiedFormula DemoBase DemoConst [] :=
  .ex .prop .top

def weakForallFree : SimpleQuantifiedFormula DemoBase DemoConst [.prop] :=
  .all .prop (.atom
    (.var (SimpleVar.vs (SimpleVar.vz : SimpleVar DemoBase [.prop] .prop))))

def truthSynSubst : SimpleSubst DemoBase DemoConst [.prop] [] :=
  SimpleSubst.cons (.const DemoConst.truth) (SimpleSubst.empty DemoBase DemoConst [])

theorem eval_forallTop :
    SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval demoQuantInterp forallTop =
      demoQuantInterp.toPropositional.top [] :=
  rfl

theorem eval_existsTop :
    SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval demoQuantInterp existsTop =
      demoQuantInterp.toPropositional.bot [] :=
  rfl

theorem eval_subst_weakForallFree :
    SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval demoQuantInterp
        (SimpleQuantifiedFormula.subst truthSynSubst weakForallFree) =
      (SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval demoQuantInterp weakForallFree).reindex
        (SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp truthSynSubst) := by
  exact
    SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval_subst
      (I := demoQuantInterp) (σs := truthSynSubst) (φ := weakForallFree)

theorem eval_forallTop_true :
    (SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval demoQuantInterp forallTop).toContinuousMap true =
      (true, true) := by
  rfl

theorem eval_existsTop_true :
    (SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval demoQuantInterp existsTop).toContinuousMap true =
      (true, false) := by
  rfl

theorem falseConst_true :
    (CtxTerm.const demoInterp [] .prop DemoConst.falsehood).toContinuousMap true = (true, false) := by
  rfl

theorem truthConst_true :
    (CtxTerm.const demoInterp [] .prop DemoConst.truth).toContinuousMap true = (true, true) := by
  rfl

theorem eval_existsTop_ne_eval_forallTop :
    SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval demoQuantInterp existsTop ≠
      SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval demoQuantInterp forallTop := by
  intro h
  have hpoint := congrArg (fun t => t.toContinuousMap true) h
  have hconst :
      (CtxTerm.const demoInterp [] .prop DemoConst.falsehood).toContinuousMap true =
        (CtxTerm.const demoInterp [] .prop DemoConst.truth).toContinuousMap true := by
    change
      (SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval demoQuantInterp existsTop).toContinuousMap true =
        (SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval demoQuantInterp forallTop).toContinuousMap true
    exact hpoint
  rw [falseConst_true, truthConst_true] at hconst
  cases hconst

end AwodeyButzQuantifiedTopologicalFragmentRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
