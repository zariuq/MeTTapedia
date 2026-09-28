import Mettapedia.Languages.Agda.Structural.Reduction
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalPolynomial
import Mettapedia.OSLF.Syntax.PositionEnumeration

/-!
# Local rule data for elimination-spine computation

Each rule declares only its own parameters. The beta body has one term
argument; the remaining spine is a separate parameter. Computation uses
metavariable application supplied by the generic binding signature.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Authored

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

abbrev Schema (M : List (MetaArity sig)) := withMetas sig M
abbrev STerm (M : List (MetaArity sig)) (Γ : Ctx sig) (s : Srt) := Term (Schema M) Γ s

def lamS {M Γ} (body : STerm M (.term :: Γ) .term) : STerm M Γ .term :=
  .op (Sum.inl Op.lam) (.cons body .nil)
def lamNoAbsS {M Γ} (body : STerm M Γ .term) : STerm M Γ .term :=
  .op (Sum.inl Op.lamNoAbs) (.cons body .nil)
def eliminateS {M Γ} (head : STerm M Γ .term) (spine : STerm M Γ .spine) :
    STerm M Γ .term := .op (Sum.inl Op.eliminate) (.cons head (.cons spine .nil))
def applyS {M Γ} (argument : STerm M Γ .term) : STerm M Γ .elim :=
  .op (Sum.inl Op.apply) (.cons argument .nil)
def nilS {M Γ} : STerm M Γ .spine := .op (Sum.inl Op.nil) .nil
def consS {M Γ} (head : STerm M Γ .elim) (tail : STerm M Γ .spine) :
    STerm M Γ .spine := .op (Sum.inl Op.cons) (.cons head (.cons tail .nil))
def appendS {M Γ} (first second : STerm M Γ .spine) : STerm M Γ .spine :=
  .op (Sum.inl Op.append) (.cons first (.cons second .nil))

def rootRule {M : List (MetaArity sig)} {s : Srt}
    (lhs rhs : STerm M [] s) : IntrinsicScopedConditionalPolynomial.Rule sig M where
  conclusion := ⟨[], s, lhs, rhs, rootPosition lhs⟩
  premises := []

abbrev betaMetas : List (MetaArity sig) :=
  [([Srt.term], Srt.term), ([], Srt.term), ([], Srt.spine)]
def betaBody {Γ} (argument : STerm betaMetas Γ .term) : STerm betaMetas Γ .term :=
  .op (Sum.inr (MetaOp.mk (M := betaMetas) 0)) (.cons argument .nil)
def betaArgument {Γ} : STerm betaMetas Γ .term :=
  .op (Sum.inr (MetaOp.mk (M := betaMetas) 1)) .nil
def betaRest {Γ} : STerm betaMetas Γ .spine :=
  .op (Sum.inr (MetaOp.mk (M := betaMetas) 2)) .nil

def beta := rootRule
  (eliminateS (lamS (betaBody (.var .zero))) (consS (applyS betaArgument) betaRest))
  (eliminateS (betaBody betaArgument) betaRest)

abbrev betaNoAbsMetas : List (MetaArity sig) :=
  [([], Srt.term), ([], Srt.term), ([], Srt.spine)]
def noAbsBody {Γ} : STerm betaNoAbsMetas Γ .term :=
  .op (Sum.inr (MetaOp.mk (M := betaNoAbsMetas) 0)) .nil
def noAbsArgument {Γ} : STerm betaNoAbsMetas Γ .term :=
  .op (Sum.inr (MetaOp.mk (M := betaNoAbsMetas) 1)) .nil
def noAbsRest {Γ} : STerm betaNoAbsMetas Γ .spine :=
  .op (Sum.inr (MetaOp.mk (M := betaNoAbsMetas) 2)) .nil

def betaNoAbs := rootRule
  (eliminateS (lamNoAbsS noAbsBody) (consS (applyS noAbsArgument) noAbsRest))
  (eliminateS noAbsBody noAbsRest)

abbrev emptyMetas : List (MetaArity sig) := [([], Srt.term)]
def emptyHead {Γ} : STerm emptyMetas Γ .term :=
  .op (Sum.inr (MetaOp.mk (M := emptyMetas) 0)) .nil

def eliminateEmpty := rootRule (eliminateS emptyHead nilS) emptyHead

abbrev elimAppendMetas : List (MetaArity sig) :=
  [([], Srt.term), ([], Srt.spine), ([], Srt.spine)]
def appendHead {Γ} : STerm elimAppendMetas Γ .term :=
  .op (Sum.inr (MetaOp.mk (M := elimAppendMetas) 0)) .nil
def appendFirst {Γ} : STerm elimAppendMetas Γ .spine :=
  .op (Sum.inr (MetaOp.mk (M := elimAppendMetas) 1)) .nil
def appendSecond {Γ} : STerm elimAppendMetas Γ .spine :=
  .op (Sum.inr (MetaOp.mk (M := elimAppendMetas) 2)) .nil

def eliminateAppend := rootRule
  (eliminateS (eliminateS appendHead appendFirst) appendSecond)
  (eliminateS appendHead (appendS appendFirst appendSecond))

abbrev appendEmptyMetas : List (MetaArity sig) := [([], Srt.spine)]
def appendEmptyRest {Γ} : STerm appendEmptyMetas Γ .spine :=
  .op (Sum.inr (MetaOp.mk (M := appendEmptyMetas) 0)) .nil

def appendEmpty := rootRule (appendS nilS appendEmptyRest) appendEmptyRest

abbrev appendConsMetas : List (MetaArity sig) :=
  [([], Srt.elim), ([], Srt.spine), ([], Srt.spine)]
def appendConsHead {Γ} : STerm appendConsMetas Γ .elim :=
  .op (Sum.inr (MetaOp.mk (M := appendConsMetas) 0)) .nil
def appendConsFirst {Γ} : STerm appendConsMetas Γ .spine :=
  .op (Sum.inr (MetaOp.mk (M := appendConsMetas) 1)) .nil
def appendConsSecond {Γ} : STerm appendConsMetas Γ .spine :=
  .op (Sum.inr (MetaOp.mk (M := appendConsMetas) 2)) .nil

def appendCons := rootRule (appendS (consS appendConsHead appendConsFirst) appendConsSecond)
  (consS appendConsHead (appendS appendConsFirst appendConsSecond))

/-- Six computational/administrative declarations, with six local telescopes. -/
def roots : List (LocalRule sig) :=
  [⟨betaMetas, beta⟩, ⟨betaNoAbsMetas, betaNoAbs⟩, ⟨emptyMetas, eliminateEmpty⟩,
   ⟨elimAppendMetas, eliminateAppend⟩, ⟨appendEmptyMetas, appendEmpty⟩,
   ⟨appendConsMetas, appendCons⟩]

theorem root_inventory : roots.length = 6 := rfl

theorem telescope_sizes : roots.map (fun rule => rule.1.length) = [3, 3, 1, 3, 1, 3] := rfl

theorem no_root_premises (index : Fin roots.length) :
    (roots.get index).2.premises = [] := by
  rcases index with ⟨i, h⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | n + 6 => simp only [roots, List.length_cons, List.length_nil] at h; omega

end Mettapedia.Languages.Agda.Structural.Authored
