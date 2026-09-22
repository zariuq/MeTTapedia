import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceipt
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionParallelSpine

/-!
# Executable inversion of native parallel receipts

Rigid constructor and under-applied eliminator spines admit only structural
parallel development. Inversion inspects the supplied receipt tree and retains
its actual component receipts. No witnesses are extracted from propositional
support, and no conversion search is performed.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt

open Presentation NativeIndexedFamilies
open NativeRelatorConversionParallel (spine spineHead spineDepth Rigidity)

variable {n : Nat}

/-- Ordered component evidence, retained in Type rather than propositional support. -/
inductive ArgumentReceipts : List (Tower.Tm n) → List (Tower.Tm n) → Type where
  | nil : ArgumentReceipts [] []
  | cons {source target : Tower.Tm n} {sources targets : List (Tower.Tm n)} :
      Receipt source target → ArgumentReceipts sources targets →
        ArgumentReceipts (source :: sources) (target :: targets)

private def spineViewAux {source target : Tower.Tm n} (receipt : Receipt source target) :
    ∀ name arguments, source = spine name arguments →
      Rigidity name arguments.length →
      Σ arguments', PLift (target = spine name arguments') × ArgumentReceipts arguments arguments' :=
  match receipt with
  | .const original => by
      intro name arguments equality _
      cases arguments with
      | nil => cases equality; exact ⟨[], ⟨rfl⟩, .nil⟩
      | cons argument rest => cases equality
  | .app functionStep argumentStep => by
      intro name arguments equality rigid
      cases arguments with
      | nil => cases equality
      | cons first rest =>
          cases equality
          obtain ⟨rest', ⟨shape⟩, arguments⟩ := spineViewAux functionStep name rest rfl rigid.shorten
          exact ⟨_ :: rest', ⟨by simp only [spine, shape]⟩, .cons argumentStep arguments⟩
  | .listNil _ _ _ _ _ => by
      intro name arguments equality rigid
      have names : Intrinsic.eliminateName = name := by
        simpa only [Intrinsic.eliminateApp, spineHead, NativeRelatorConversionParallel.spineHead_spine,
          Option.some.injEq] using congrArg spineHead equality
      have counts : 5 = arguments.length := by
        simpa only [Intrinsic.eliminateApp, spineDepth, NativeRelatorConversionParallel.spineDepth_spine]
          using congrArg spineDepth equality
      apply False.elim
      rcases rigid.1 with different | short
      · exact different names.symm
      · omega
  | .listCons _ _ _ _ _ _ _ => by
      intro name arguments equality rigid
      have names : Intrinsic.eliminateName = name := by
        simpa only [Intrinsic.eliminateApp, spineHead, NativeRelatorConversionParallel.spineHead_spine,
          Option.some.injEq] using congrArg spineHead equality
      have counts : 5 = arguments.length := by
        simpa only [Intrinsic.eliminateApp, spineDepth, NativeRelatorConversionParallel.spineDepth_spine]
          using congrArg spineDepth equality
      apply False.elim
      rcases rigid.1 with different | short
      · exact different names.symm
      · omega
  | .identity _ _ _ _ _ _ _ _ => by
      intro name arguments equality rigid
      have names : Intrinsic.identityEliminateName = name := by
        simpa only [Intrinsic.identityEliminateApp, spineHead, NativeRelatorConversionParallel.spineHead_spine,
          Option.some.injEq] using congrArg spineHead equality
      have counts : 6 = arguments.length := by
        simpa only [Intrinsic.identityEliminateApp, spineDepth, NativeRelatorConversionParallel.spineDepth_spine]
          using congrArg spineDepth equality
      apply False.elim
      rcases rigid.2.1 with different | short
      · exact different names.symm
      · omega
  | .relNil _ _ _ _ _ _ _ _ _ _ _ _ _ => by
      intro name arguments equality rigid
      have names : IntrinsicRelator.eliminateName = name := by
        simpa only [IntrinsicRelator.eliminateApp, spineHead, NativeRelatorConversionParallel.spineHead_spine,
          Option.some.injEq] using congrArg spineHead equality
      have counts : 9 = arguments.length := by
        simpa only [IntrinsicRelator.eliminateApp, spineDepth, NativeRelatorConversionParallel.spineDepth_spine]
          using congrArg spineDepth equality
      apply False.elim
      rcases rigid.2.2 with different | short
      · exact different names.symm
      · omega
  | .relCons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
      intro name arguments equality rigid
      have names : IntrinsicRelator.eliminateName = name := by
        simpa only [IntrinsicRelator.eliminateApp, spineHead, NativeRelatorConversionParallel.spineHead_spine,
          Option.some.injEq] using congrArg spineHead equality
      have counts : 9 = arguments.length := by
        simpa only [IntrinsicRelator.eliminateApp, spineDepth, NativeRelatorConversionParallel.spineDepth_spine]
          using congrArg spineDepth equality
      apply False.elim
      rcases rigid.2.2 with different | short
      · exact different names.symm
      · omega
  | .var _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .head _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .headRel _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .pi _ _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .sigma _ _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .id _ _ _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .lam _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .pair _ _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .fst _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .snd _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .refl _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .betaPi _ _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .betaSigmaFst _ _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible
  | .betaSigmaSnd _ _ => by
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, NativeRelatorConversionParallel.spineHead_spine] at impossible
      cases impossible

/-- Compute all target arguments and their original ordered receipts. -/
def spineView (name : DeclName) (arguments : List (Tower.Tm n))
    (rigid : Rigidity name arguments.length)
    {target : Tower.Tm n} (receipt : Receipt (spine name arguments) target) :
    Σ arguments', PLift (target = spine name arguments') × ArgumentReceipts arguments arguments' :=
  spineViewAux receipt name arguments rfl rigid

def listPrefixView {x0 x1 x2 x3 target : Tower.Tm n}
    (receipt : Receipt (NativeRelatorConversionParallel.listPrefix x0 x1 x2 x3) target) :
    Σ (x0' x1' x2' x3' : Tower.Tm n),
      PLift (target = NativeRelatorConversionParallel.listPrefix x0' x1' x2' x3') ×
        Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' × Receipt x3 x3' := by
  obtain ⟨arguments, shape, steps⟩ := spineView Intrinsic.eliminateName
    [x3, x2, x1, x0] (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h3 steps =>
    cases steps with | cons h2 steps =>
      cases steps with | cons h1 steps =>
        cases steps with | cons h0 steps =>
          cases steps
          exact ⟨_, _, _, _, shape, h0, h1, h2, h3⟩

def identityPrefixView {x0 x1 x2 x3 x4 target : Tower.Tm n}
    (receipt : Receipt (NativeRelatorConversionParallel.identityPrefix x0 x1 x2 x3 x4) target) :
    Σ (x0' x1' x2' x3' x4' : Tower.Tm n),
      PLift (target = NativeRelatorConversionParallel.identityPrefix x0' x1' x2' x3' x4') ×
        Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' × Receipt x3 x3' × Receipt x4 x4' := by
  obtain ⟨arguments, shape, steps⟩ := spineView Intrinsic.identityEliminateName
    [x4, x3, x2, x1, x0] (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h4 steps =>
    cases steps with | cons h3 steps =>
      cases steps with | cons h2 steps =>
        cases steps with | cons h1 steps =>
          cases steps with | cons h0 steps =>
            cases steps
            exact ⟨_, _, _, _, _, shape, h0, h1, h2, h3, h4⟩

def relPrefixView {x0 x1 x2 x3 x4 x5 x6 x7 target : Tower.Tm n}
    (receipt : Receipt (NativeRelatorConversionParallel.relPrefix x0 x1 x2 x3 x4 x5 x6 x7) target) :
    Σ (x0' x1' x2' x3' x4' x5' x6' x7' : Tower.Tm n),
      PLift (target = NativeRelatorConversionParallel.relPrefix x0' x1' x2' x3' x4' x5' x6' x7') ×
        Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' × Receipt x3 x3' × Receipt x4 x4' × Receipt x5 x5' × Receipt x6 x6' × Receipt x7 x7' := by
  obtain ⟨arguments, shape, steps⟩ := spineView IntrinsicRelator.eliminateName
    [x7, x6, x5, x4, x3, x2, x1, x0] (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h7 steps =>
    cases steps with | cons h6 steps =>
      cases steps with | cons h5 steps =>
        cases steps with | cons h4 steps =>
          cases steps with | cons h3 steps =>
            cases steps with | cons h2 steps =>
              cases steps with | cons h1 steps =>
                cases steps with | cons h0 steps =>
                  cases steps
                  exact ⟨_, _, _, _, _, _, _, _, shape, h0, h1, h2, h3, h4, h5, h6, h7⟩

def nilView {x0 target : Tower.Tm n}
    (receipt : Receipt (Intrinsic.nilApp x0) target) :
    Σ (x0' : Tower.Tm n),
      PLift (target = Intrinsic.nilApp x0') ×
        Receipt x0 x0' := by
  obtain ⟨arguments, shape, steps⟩ := spineView Intrinsic.nilName
    [x0] (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h0 steps =>
    cases steps
    exact ⟨_, shape, h0⟩

def consView {x0 x1 x2 target : Tower.Tm n}
    (receipt : Receipt (Intrinsic.consApp x0 x1 x2) target) :
    Σ (x0' x1' x2' : Tower.Tm n),
      PLift (target = Intrinsic.consApp x0' x1' x2') ×
        Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' := by
  obtain ⟨arguments, shape, steps⟩ := spineView Intrinsic.consName
    [x2, x1, x0] (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h2 steps =>
    cases steps with | cons h1 steps =>
      cases steps with | cons h0 steps =>
        cases steps
        exact ⟨_, _, _, shape, h0, h1, h2⟩

def nilRelView {x0 x1 x2 target : Tower.Tm n}
    (receipt : Receipt (IntrinsicRelator.nilRelApp x0 x1 x2) target) :
    Σ (x0' x1' x2' : Tower.Tm n),
      PLift (target = IntrinsicRelator.nilRelApp x0' x1' x2') ×
        Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' := by
  obtain ⟨arguments, shape, steps⟩ := spineView IntrinsicRelator.nilRelName
    [x2, x1, x0] (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h2 steps =>
    cases steps with | cons h1 steps =>
      cases steps with | cons h0 steps =>
        cases steps
        exact ⟨_, _, _, shape, h0, h1, h2⟩

def consRelView {x0 x1 x2 x3 x4 x5 x6 x7 x8 target : Tower.Tm n}
    (receipt : Receipt (IntrinsicRelator.consRelApp x0 x1 x2 x3 x4 x5 x6 x7 x8) target) :
    Σ (x0' x1' x2' x3' x4' x5' x6' x7' x8' : Tower.Tm n),
      PLift (target = IntrinsicRelator.consRelApp x0' x1' x2' x3' x4' x5' x6' x7' x8') ×
        Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' × Receipt x3 x3' × Receipt x4 x4' × Receipt x5 x5' × Receipt x6 x6' × Receipt x7 x7' × Receipt x8 x8' := by
  obtain ⟨arguments, shape, steps⟩ := spineView IntrinsicRelator.consRelName
    [x8, x7, x6, x5, x4, x3, x2, x1, x0] (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h8 steps =>
    cases steps with | cons h7 steps =>
      cases steps with | cons h6 steps =>
        cases steps with | cons h5 steps =>
          cases steps with | cons h4 steps =>
            cases steps with | cons h3 steps =>
              cases steps with | cons h2 steps =>
                cases steps with | cons h1 steps =>
                  cases steps with | cons h0 steps =>
                    cases steps
                    exact ⟨_, _, _, _, _, _, _, _, _, shape, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

def lamView {body : Tower.Tm (n + 1)} {target : Tower.Tm n}
    (receipt : Receipt (.lam body) target) :
    Σ body', PLift (target = .lam body') × Receipt body body' := by
  cases receipt with
  | lam inner => exact ⟨_, ⟨rfl⟩, inner⟩

def pairView {first second target : Tower.Tm n}
    (receipt : Receipt (.pair first second) target) :
    Σ first' second', PLift (target = .pair first' second') ×
      Receipt first first' × Receipt second second' := by
  cases receipt with
  | pair left right => exact ⟨_, _, ⟨rfl⟩, left, right⟩

def reflView {term target : Tower.Tm n} (receipt : Receipt (.refl term) target) :
    Σ term', PLift (target = .refl term') × Receipt term term' := by
  cases receipt with
  | refl inner => exact ⟨_, ⟨rfl⟩, inner⟩


def lamToFixed {body body' : Tower.Tm (n + 1)}
    (receipt : Receipt (.lam body) (.lam body')) : Receipt body body' := by
  cases receipt with | lam inner => exact inner

def pairToFixed {first second first' second' : Tower.Tm n}
    (receipt : Receipt (.pair first second) (.pair first' second')) :
    Receipt first first' × Receipt second second' := by
  cases receipt with | pair left right => exact ⟨left, right⟩

/-- Inversion at a known target spine preserves its exact argument positions. -/
def spineToFixed (name : DeclName) (arguments targets : List (Tower.Tm n))
    (rigid : Rigidity name arguments.length)
    (receipt : Receipt (spine name arguments) (spine name targets)) :
    ArgumentReceipts arguments targets := by
  obtain ⟨actual, ⟨shape⟩, steps⟩ := spineView name arguments rigid receipt
  have equality := NativeRelatorConversionParallel.spine_injective name shape
  cases equality
  exact steps

def listPrefixToFixed {x0 x1 x2 x3 x0' x1' x2' x3' : Tower.Tm n}
    (receipt : Receipt (NativeRelatorConversionParallel.listPrefix x0 x1 x2 x3) (NativeRelatorConversionParallel.listPrefix x0' x1' x2' x3')) :
    Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' × Receipt x3 x3' := by
  have steps := spineToFixed Intrinsic.eliminateName
    [x3, x2, x1, x0] [x3', x2', x1', x0']
    (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h3 steps =>
    cases steps with | cons h2 steps =>
      cases steps with | cons h1 steps =>
        cases steps with | cons h0 steps =>
          cases steps
          exact ⟨h0, h1, h2, h3⟩

def Receipt.listPrefixCong {x0 x1 x2 x3 x0' x1' x2' x3' : Tower.Tm n}
    (h0 : Receipt x0 x0') (h1 : Receipt x1 x1') (h2 : Receipt x2 x2') (h3 : Receipt x3 x3') :
    Receipt (NativeRelatorConversionParallel.listPrefix x0 x1 x2 x3) (NativeRelatorConversionParallel.listPrefix x0' x1' x2' x3') :=
  (.app (.app (.app (.app (.const Intrinsic.eliminateName) h0) h1) h2) h3)

def identityPrefixToFixed {x0 x1 x2 x3 x4 x0' x1' x2' x3' x4' : Tower.Tm n}
    (receipt : Receipt (NativeRelatorConversionParallel.identityPrefix x0 x1 x2 x3 x4) (NativeRelatorConversionParallel.identityPrefix x0' x1' x2' x3' x4')) :
    Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' × Receipt x3 x3' × Receipt x4 x4' := by
  have steps := spineToFixed Intrinsic.identityEliminateName
    [x4, x3, x2, x1, x0] [x4', x3', x2', x1', x0']
    (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h4 steps =>
    cases steps with | cons h3 steps =>
      cases steps with | cons h2 steps =>
        cases steps with | cons h1 steps =>
          cases steps with | cons h0 steps =>
            cases steps
            exact ⟨h0, h1, h2, h3, h4⟩

def Receipt.identityPrefixCong {x0 x1 x2 x3 x4 x0' x1' x2' x3' x4' : Tower.Tm n}
    (h0 : Receipt x0 x0') (h1 : Receipt x1 x1') (h2 : Receipt x2 x2') (h3 : Receipt x3 x3') (h4 : Receipt x4 x4') :
    Receipt (NativeRelatorConversionParallel.identityPrefix x0 x1 x2 x3 x4) (NativeRelatorConversionParallel.identityPrefix x0' x1' x2' x3' x4') :=
  (.app (.app (.app (.app (.app (.const Intrinsic.identityEliminateName) h0) h1) h2) h3) h4)

def relPrefixToFixed {x0 x1 x2 x3 x4 x5 x6 x7 x0' x1' x2' x3' x4' x5' x6' x7' : Tower.Tm n}
    (receipt : Receipt (NativeRelatorConversionParallel.relPrefix x0 x1 x2 x3 x4 x5 x6 x7) (NativeRelatorConversionParallel.relPrefix x0' x1' x2' x3' x4' x5' x6' x7')) :
    Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' × Receipt x3 x3' × Receipt x4 x4' × Receipt x5 x5' × Receipt x6 x6' × Receipt x7 x7' := by
  have steps := spineToFixed IntrinsicRelator.eliminateName
    [x7, x6, x5, x4, x3, x2, x1, x0] [x7', x6', x5', x4', x3', x2', x1', x0']
    (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h7 steps =>
    cases steps with | cons h6 steps =>
      cases steps with | cons h5 steps =>
        cases steps with | cons h4 steps =>
          cases steps with | cons h3 steps =>
            cases steps with | cons h2 steps =>
              cases steps with | cons h1 steps =>
                cases steps with | cons h0 steps =>
                  cases steps
                  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

def Receipt.relPrefixCong {x0 x1 x2 x3 x4 x5 x6 x7 x0' x1' x2' x3' x4' x5' x6' x7' : Tower.Tm n}
    (h0 : Receipt x0 x0') (h1 : Receipt x1 x1') (h2 : Receipt x2 x2') (h3 : Receipt x3 x3') (h4 : Receipt x4 x4') (h5 : Receipt x5 x5') (h6 : Receipt x6 x6') (h7 : Receipt x7 x7') :
    Receipt (NativeRelatorConversionParallel.relPrefix x0 x1 x2 x3 x4 x5 x6 x7) (NativeRelatorConversionParallel.relPrefix x0' x1' x2' x3' x4' x5' x6' x7') :=
  (.app (.app (.app (.app (.app (.app (.app (.app (.const IntrinsicRelator.eliminateName) h0) h1) h2) h3) h4) h5) h6) h7)

def nilToFixed {x0 x0' : Tower.Tm n}
    (receipt : Receipt (Intrinsic.nilApp x0) (Intrinsic.nilApp x0')) :
    Receipt x0 x0' := by
  have steps := spineToFixed Intrinsic.nilName
    [x0] [x0']
    (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h0 steps =>
    cases steps
    exact h0

def Receipt.nilCong {x0 x0' : Tower.Tm n}
    (h0 : Receipt x0 x0') :
    Receipt (Intrinsic.nilApp x0) (Intrinsic.nilApp x0') :=
  (.app (.const Intrinsic.nilName) h0)

def consToFixed {x0 x1 x2 x0' x1' x2' : Tower.Tm n}
    (receipt : Receipt (Intrinsic.consApp x0 x1 x2) (Intrinsic.consApp x0' x1' x2')) :
    Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' := by
  have steps := spineToFixed Intrinsic.consName
    [x2, x1, x0] [x2', x1', x0']
    (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h2 steps =>
    cases steps with | cons h1 steps =>
      cases steps with | cons h0 steps =>
        cases steps
        exact ⟨h0, h1, h2⟩

def Receipt.consCong {x0 x1 x2 x0' x1' x2' : Tower.Tm n}
    (h0 : Receipt x0 x0') (h1 : Receipt x1 x1') (h2 : Receipt x2 x2') :
    Receipt (Intrinsic.consApp x0 x1 x2) (Intrinsic.consApp x0' x1' x2') :=
  (.app (.app (.app (.const Intrinsic.consName) h0) h1) h2)

def nilRelToFixed {x0 x1 x2 x0' x1' x2' : Tower.Tm n}
    (receipt : Receipt (IntrinsicRelator.nilRelApp x0 x1 x2) (IntrinsicRelator.nilRelApp x0' x1' x2')) :
    Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' := by
  have steps := spineToFixed IntrinsicRelator.nilRelName
    [x2, x1, x0] [x2', x1', x0']
    (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h2 steps =>
    cases steps with | cons h1 steps =>
      cases steps with | cons h0 steps =>
        cases steps
        exact ⟨h0, h1, h2⟩

def Receipt.nilRelCong {x0 x1 x2 x0' x1' x2' : Tower.Tm n}
    (h0 : Receipt x0 x0') (h1 : Receipt x1 x1') (h2 : Receipt x2 x2') :
    Receipt (IntrinsicRelator.nilRelApp x0 x1 x2) (IntrinsicRelator.nilRelApp x0' x1' x2') :=
  (.app (.app (.app (.const IntrinsicRelator.nilRelName) h0) h1) h2)

def consRelToFixed {x0 x1 x2 x3 x4 x5 x6 x7 x8 x0' x1' x2' x3' x4' x5' x6' x7' x8' : Tower.Tm n}
    (receipt : Receipt (IntrinsicRelator.consRelApp x0 x1 x2 x3 x4 x5 x6 x7 x8) (IntrinsicRelator.consRelApp x0' x1' x2' x3' x4' x5' x6' x7' x8')) :
    Receipt x0 x0' × Receipt x1 x1' × Receipt x2 x2' × Receipt x3 x3' × Receipt x4 x4' × Receipt x5 x5' × Receipt x6 x6' × Receipt x7 x7' × Receipt x8 x8' := by
  have steps := spineToFixed IntrinsicRelator.consRelName
    [x8, x7, x6, x5, x4, x3, x2, x1, x0] [x8', x7', x6', x5', x4', x3', x2', x1', x0']
    (by simp only [Rigidity, List.length_cons, List.length_nil]; decide) receipt
  cases steps with | cons h8 steps =>
    cases steps with | cons h7 steps =>
      cases steps with | cons h6 steps =>
        cases steps with | cons h5 steps =>
          cases steps with | cons h4 steps =>
            cases steps with | cons h3 steps =>
              cases steps with | cons h2 steps =>
                cases steps with | cons h1 steps =>
                  cases steps with | cons h0 steps =>
                    cases steps
                    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

def Receipt.consRelCong {x0 x1 x2 x3 x4 x5 x6 x7 x8 x0' x1' x2' x3' x4' x5' x6' x7' x8' : Tower.Tm n}
    (h0 : Receipt x0 x0') (h1 : Receipt x1 x1') (h2 : Receipt x2 x2') (h3 : Receipt x3 x3') (h4 : Receipt x4 x4') (h5 : Receipt x5 x5') (h6 : Receipt x6 x6') (h7 : Receipt x7 x7') (h8 : Receipt x8 x8') :
    Receipt (IntrinsicRelator.consRelApp x0 x1 x2 x3 x4 x5 x6 x7 x8) (IntrinsicRelator.consRelApp x0' x1' x2' x3' x4' x5' x6' x7' x8') :=
  (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const IntrinsicRelator.consRelName) h0) h1) h2) h3) h4) h5) h6) h7) h8)

#print axioms spineView
#print axioms listPrefixView
#print axioms relPrefixView
#print axioms consRelView
#print axioms lamView

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt
