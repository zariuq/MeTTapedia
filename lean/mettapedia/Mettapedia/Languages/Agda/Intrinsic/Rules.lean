import Mettapedia.Languages.Agda.Intrinsic.Syntax
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels
import Mettapedia.OSLF.Syntax.PositionEnumeration

/-!
# Authored Agda computation as scoped conditional rule data

The operational presentation acts on Agda terms. Metavariable dependencies
are structural: a body accepts one locally bound argument. Each congruence
premise records its own binder context. No shifting or substitution judgment
is authored here; instantiation uses the generic binding clone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic.Authored

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial

abbrev metas : List (MetaArity sig) :=
  [([Srt.term], Srt.term), ([Srt.term], Srt.term),
   ([], Srt.term), ([], Srt.term), ([], Srt.term),
   ([], Srt.term), ([], Srt.term), ([], Srt.term)]

abbrev schema := withMetas sig metas
abbrev STm (Γ : Ctx schema) := Term schema Γ .term

def m0 {Γ : Ctx schema} : STm Γ :=
  .op (Sum.inr (MetaOp.mk (M := metas) 2)) .nil
def m1 {Γ : Ctx schema} : STm Γ :=
  .op (Sum.inr (MetaOp.mk (M := metas) 3)) .nil
def m2 {Γ : Ctx schema} : STm Γ :=
  .op (Sum.inr (MetaOp.mk (M := metas) 4)) .nil
def m3 {Γ : Ctx schema} : STm Γ :=
  .op (Sum.inr (MetaOp.mk (M := metas) 5)) .nil
def m4 {Γ : Ctx schema} : STm Γ :=
  .op (Sum.inr (MetaOp.mk (M := metas) 6)) .nil
def m5 {Γ : Ctx schema} : STm Γ :=
  .op (Sum.inr (MetaOp.mk (M := metas) 7)) .nil
def b0 {Γ : Ctx schema} (arg : STm Γ) : STm Γ :=
  .op (Sum.inr (MetaOp.mk (M := metas) 0)) (.cons arg .nil)
def b1 {Γ : Ctx schema} (arg : STm Γ) : STm Γ :=
  .op (Sum.inr (MetaOp.mk (M := metas) 1)) (.cons arg .nil)

def piS {Γ : Ctx schema} (x0 : STm Γ) (x1 : STm (.term :: Γ)) : STm Γ :=
  .op (Sum.inl Op.pi) (.cons x0 (.cons x1 .nil))

def lamS {Γ : Ctx schema} (x0 : STm (.term :: Γ)) : STm Γ :=
  .op (Sum.inl Op.lam) (.cons x0 .nil)

def appS {Γ : Ctx schema} (x0 : STm Γ) (x1 : STm Γ) : STm Γ :=
  .op (Sum.inl Op.app) (.cons x0 (.cons x1 .nil))

def annS {Γ : Ctx schema} (x0 : STm Γ) (x1 : STm Γ) : STm Γ :=
  .op (Sum.inl Op.ann) (.cons x0 (.cons x1 .nil))

def sigmaS {Γ : Ctx schema} (x0 : STm Γ) (x1 : STm (.term :: Γ)) : STm Γ :=
  .op (Sum.inl Op.sigma) (.cons x0 (.cons x1 .nil))

def pairS {Γ : Ctx schema} (x0 : STm Γ) (x1 : STm Γ) : STm Γ :=
  .op (Sum.inl Op.pair) (.cons x0 (.cons x1 .nil))

def fstS {Γ : Ctx schema} (x0 : STm Γ) : STm Γ :=
  .op (Sum.inl Op.fst) (.cons x0 .nil)

def sndS {Γ : Ctx schema} (x0 : STm Γ) : STm Γ :=
  .op (Sum.inl Op.snd) (.cons x0 .nil)

def sucS {Γ : Ctx schema} (x0 : STm Γ) : STm Γ :=
  .op (Sum.inl Op.suc) (.cons x0 .nil)

def natrecS {Γ : Ctx schema} (x0 : STm Γ) (x1 : STm Γ) (x2 : STm Γ) (x3 : STm Γ) (x4 : STm Γ) : STm Γ :=
  .op (Sum.inl Op.natrec) (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))

def zeroS {Γ : Ctx schema}  : STm Γ :=
  .op (Sum.inl Op.zero) .nil

def natSucS {Γ : Ctx schema}  : STm Γ :=
  .op (Sum.inl Op.natSuc) .nil

def rootRule (lhs rhs : STm []) : Rule sig metas where
  conclusion := ⟨[], .term, lhs, rhs, rootPosition lhs⟩
  premises := []

def congrRule (lhs rhs : STm []) (binders : List Srt)
    (source target : STm (binders ++ [])) : Rule sig metas where
  conclusion := ⟨[], .term, lhs, rhs, rootPosition lhs⟩
  premises := [⟨binders, .term, source, target⟩]

def beta := rootRule (appS (lamS (b0 (.var .zero))) m0) (b0 m0)
def first := rootRule (fstS (pairS m0 m1)) m0
def second := rootRule (sndS (pairS m0 m1)) m1
def annotation := rootRule (annS m0 m1) m0
def successor := rootRule (appS natSucS m0) (sucS m0)
def recZero := rootRule (natrecS m0 m1 m2 m3 zeroS) m2
def recSuc := rootRule (natrecS m0 m1 m2 m3 (sucS m4))
  (appS (appS m3 m4) (natrecS m0 m1 m2 m3 m4))

def piCong0 := congrRule (piS m0 (b0 (.var .zero)))
  (piS m1 (b0 (.var .zero))) [] m0 m1

def piCong1 := congrRule (piS m2 (b0 (.var .zero)))
  (piS m2 (b1 (.var .zero))) [.term] (b0 (.var .zero)) (b1 (.var .zero))

def lamCong0 := congrRule (lamS (b0 (.var .zero)))
  (lamS (b1 (.var .zero))) [.term] (b0 (.var .zero)) (b1 (.var .zero))

def appCong0 := congrRule (appS m0 m2)
  (appS m1 m2) [] m0 m1

def appCong1 := congrRule (appS m2 m0)
  (appS m2 m1) [] m0 m1

def annCong0 := congrRule (annS m0 m2)
  (annS m1 m2) [] m0 m1

def annCong1 := congrRule (annS m2 m0)
  (annS m2 m1) [] m0 m1

def sigmaCong0 := congrRule (sigmaS m0 (b0 (.var .zero)))
  (sigmaS m1 (b0 (.var .zero))) [] m0 m1

def sigmaCong1 := congrRule (sigmaS m2 (b0 (.var .zero)))
  (sigmaS m2 (b1 (.var .zero))) [.term] (b0 (.var .zero)) (b1 (.var .zero))

def pairCong0 := congrRule (pairS m0 m2)
  (pairS m1 m2) [] m0 m1

def pairCong1 := congrRule (pairS m2 m0)
  (pairS m2 m1) [] m0 m1

def fstCong0 := congrRule (fstS m0)
  (fstS m1) [] m0 m1

def sndCong0 := congrRule (sndS m0)
  (sndS m1) [] m0 m1

def sucCong0 := congrRule (sucS m0)
  (sucS m1) [] m0 m1

def natrecCong0 := congrRule (natrecS m0 m2 m3 m4 m5)
  (natrecS m1 m2 m3 m4 m5) [] m0 m1

def natrecCong1 := congrRule (natrecS m2 m0 m3 m4 m5)
  (natrecS m2 m1 m3 m4 m5) [] m0 m1

def natrecCong2 := congrRule (natrecS m2 m3 m0 m4 m5)
  (natrecS m2 m3 m1 m4 m5) [] m0 m1

def natrecCong3 := congrRule (natrecS m2 m3 m4 m0 m5)
  (natrecS m2 m3 m4 m1 m5) [] m0 m1

def natrecCong4 := congrRule (natrecS m2 m3 m4 m5 m0)
  (natrecS m2 m3 m4 m5 m1) [] m0 m1

/-- Seven root computations and nineteen binder-aware congruences. -/
def rules : List (Rule sig metas) :=
  [beta, first, second, annotation, successor, recZero, recSuc, piCong0, piCong1, lamCong0, appCong0, appCong1, annCong0, annCong1, sigmaCong0, sigmaCong1, pairCong0, pairCong1, fstCong0, sndCong0, sucCong0, natrecCong0, natrecCong1, natrecCong2, natrecCong3, natrecCong4]

theorem rule_inventory : rules.length = 26 := rfl

end Mettapedia.Languages.Agda.Intrinsic.Authored
