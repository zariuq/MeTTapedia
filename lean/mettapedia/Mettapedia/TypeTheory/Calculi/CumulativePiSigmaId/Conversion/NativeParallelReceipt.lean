import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCompletedRootCertificate
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionParallel

/-!
# Proof-retaining native parallel development

Receipts retain the selected parallel rule and checked finite certificates for
all metadata-conversion guards. Their propositional support is exactly the
existing completed parallel relation. Replaying a receipt computes a checked
conversion code for the original authored rules, including every native branch.
That code is an observation of the receipt: developments discarded by a native
contraction need not occur in the resulting authored conversion. The receipt
itself retains those selections independently.

This is the evidence representation and authored replay required by a computed
parallel diamond; it does not itself supply that diamond.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt

open Presentation StructuralConversionCode NativeIndexedFamilies
open NativeCompletedRootCertificate NativeRelatorConversionCompletion

inductive Receipt : {n : Nat} → Tower.Tm n → Tower.Tm n → Type where
  | var {n : Nat} (index : Fin n) : Receipt (.var index) (.var index)
  | const {n : Nat} (name : DeclName) : Receipt (.const name : Tower.Tm n) (.const name)
  | head {n : Nat} (value : Tower.Head) : Receipt (.head value : Tower.Tm n) (.head value)
  | headRel {n : Nat} {left right : Tower.Head} :
      Tower.HeadEq left right → Receipt (.head left : Tower.Tm n) (.head right)
  | pi {n : Nat} {domain domain' : Tower.Tm n} {codomain codomain' : Tower.Tm (n + 1)} :
      Receipt domain domain' → Receipt codomain codomain' →
        Receipt (.pi domain codomain) (.pi domain' codomain')
  | sigma {n : Nat} {domain domain' : Tower.Tm n} {codomain codomain' : Tower.Tm (n + 1)} :
      Receipt domain domain' → Receipt codomain codomain' →
        Receipt (.sigma domain codomain) (.sigma domain' codomain')
  | id {n : Nat} {type type' left left' right right' : Tower.Tm n} :
      Receipt type type' → Receipt left left' → Receipt right right' →
        Receipt (.id type left right) (.id type' left' right')
  | lam {n : Nat} {body body' : Tower.Tm (n + 1)} : Receipt body body' → Receipt (.lam body) (.lam body')
  | app {n : Nat} {function function' argument argument' : Tower.Tm n} :
      Receipt function function' → Receipt argument argument' →
        Receipt (.app function argument) (.app function' argument')
  | pair {n : Nat} {first first' second second' : Tower.Tm n} :
      Receipt first first' → Receipt second second' → Receipt (.pair first second) (.pair first' second')
  | fst {n : Nat} {pair pair' : Tower.Tm n} : Receipt pair pair' → Receipt (.fst pair) (.fst pair')
  | snd {n : Nat} {pair pair' : Tower.Tm n} : Receipt pair pair' → Receipt (.snd pair) (.snd pair')
  | refl {n : Nat} {term term' : Tower.Tm n} : Receipt term term' → Receipt (.refl term) (.refl term')
  | betaPi {n : Nat} {body body' : Tower.Tm (n + 1)} {argument argument' : Tower.Tm n} :
      Receipt body body' → Receipt argument argument' →
        Receipt (.app (.lam body) argument) (inst0 argument' body')
  | betaSigmaFst {n : Nat} {first first' second second' : Tower.Tm n} :
      Receipt first first' → Receipt second second' → Receipt (.fst (.pair first second)) first'
  | betaSigmaSnd {n : Nat} {first first' second second' : Tower.Tm n} :
      Receipt first first' → Receipt second second' → Receipt (.snd (.pair first second)) second'
  | listNil {n : Nat} {a p z s innerA a' p' z' s' : Tower.Tm n} :
      Certificate innerA a →
      Receipt a a' → Receipt p p' → Receipt z z' → Receipt s s' →
      Receipt (Intrinsic.eliminateApp a p z s (Intrinsic.nilApp innerA)) (z')
  | listCons {n : Nat} {a p z s innerA h t a' p' z' s' h' t' : Tower.Tm n} :
      Certificate innerA a →
      Receipt a a' → Receipt p p' → Receipt z z' → Receipt s s' → Receipt h h' → Receipt t t' →
      Receipt (Intrinsic.eliminateApp a p z s (Intrinsic.consApp innerA h t)) (.app (.app (.app s' h') t') (Intrinsic.eliminateApp a' p' z' s' t'))
  | identity {n : Nat} {a x p d y witness a' x' p' d' y' witness' : Tower.Tm n} :
      Certificate y x → Certificate witness x →
      Receipt a a' → Receipt x x' → Receipt p p' → Receipt d d' → Receipt y y' → Receipt witness witness' →
      Receipt (Intrinsic.identityEliminateApp a x p d y (.refl witness)) (d')
  | relNil {n : Nat} {a b r p z s xs ys innerA innerB innerR a' b' r' p' z' s' xs' ys' : Tower.Tm n} :
      Certificate innerA a → Certificate innerB b → Certificate innerR r → Certificate xs (Intrinsic.nilApp a) → Certificate ys (Intrinsic.nilApp b) →
      Receipt a a' → Receipt b b' → Receipt r r' → Receipt p p' → Receipt z z' → Receipt s s' → Receipt xs xs' → Receipt ys ys' →
      Receipt (IntrinsicRelator.eliminateApp a b r p z s xs ys (IntrinsicRelator.nilRelApp innerA innerB innerR)) (z')
  | relCons {n : Nat} {a b r p z s xs ys innerA innerB innerR h k t u he te a' b' r' p' z' s' xs' ys' h' k' t' u' he' te' : Tower.Tm n} :
      Certificate innerA a → Certificate innerB b → Certificate innerR r → Certificate xs (Intrinsic.consApp a h t) → Certificate ys (Intrinsic.consApp b k u) →
      Receipt a a' → Receipt b b' → Receipt r r' → Receipt p p' → Receipt z z' → Receipt s s' → Receipt xs xs' → Receipt ys ys' → Receipt h h' → Receipt k k' → Receipt t t' → Receipt u u' → Receipt he he' → Receipt te te' →
      Receipt (IntrinsicRelator.eliminateApp a b r p z s xs ys (IntrinsicRelator.consRelApp innerA innerB innerR h k t u he te)) (.app (.app (.app (.app (.app (.app (.app s' h') k') t') u') he') te') (IntrinsicRelator.eliminateApp a' b' r' p' z' s' t' u' te'))

namespace Receipt

def reflexive {n : Nat} : (term : Tower.Tm n) → Receipt term term
  | .var index => .var index
  | .const name => .const name
  | .head value => .head value
  | .pi domain codomain => .pi (reflexive domain) (reflexive codomain)
  | .sigma domain codomain => .sigma (reflexive domain) (reflexive codomain)
  | .id carrier left right => .id (reflexive carrier) (reflexive left) (reflexive right)
  | .lam body => .lam (reflexive body)
  | .app function argument => .app (reflexive function) (reflexive argument)
  | .pair first second => .pair (reflexive first) (reflexive second)
  | .fst inner => .fst (reflexive inner)
  | .snd inner => .snd (reflexive inner)
  | .refl term => .refl (reflexive term)

theorem support {n : Nat} {source target : Tower.Tm n} :
    Receipt source target → NativeRelatorConversionParallel.Par source target
  | .var index => .var index
  | .const name => .const name
  | .head value => .head value
  | .headRel equality => .headRel equality
  | .pi first second => .pi first.support second.support
  | .sigma first second => .sigma first.support second.support
  | .id carrier left right => .id carrier.support left.support right.support
  | .lam body => .lam body.support
  | .app function argument => .app function.support argument.support
  | .pair first second => .pair first.support second.support
  | .fst inner => .fst inner.support
  | .snd inner => .snd inner.support
  | .refl term => .refl term.support
  | .betaPi body argument => .betaPi body.support argument.support
  | .betaSigmaFst first second => .betaSigmaFst first.support second.support
  | .betaSigmaSnd first second => .betaSigmaSnd first.support second.support
  | .listNil ca a p z s => .listNil (sound ca) a.support p.support z.support s.support
  | .listCons ca a p z s h t => .listCons (sound ca) a.support p.support z.support s.support h.support t.support
  | .identity cy cw a x p d y witness => .identity (sound cy) (sound cw) a.support x.support p.support d.support y.support witness.support
  | .relNil ca cb cr cx cy a b r p z s xs ys => .relNil (sound ca) (sound cb) (sound cr) (sound cx) (sound cy)
      a.support b.support r.support p.support z.support s.support xs.support ys.support
  | .relCons ca cb cr cx cy a b r p z s xs ys h k t u he te => .relCons (sound ca) (sound cb) (sound cr) (sound cx) (sound cy)
      a.support b.support r.support p.support z.support s.support xs.support ys.support
      h.support k.support t.support u.support he.support te.support

/-- Compute the authored conversion code; metadata guards are supplied data,
not recovered by selecting witnesses from the support theorem. -/
def toCertificate {n : Nat} {source target : Tower.Tm n} :
    Receipt source target → NativeCompletedRootCertificate.Certificate source target
  | .var index => .refl _
  | .const name => .refl _
  | .head value => .refl _
  | @Receipt.headRel _ left right equality => .single (.head left right) (by simp [StepCode.check, StepCode.decode, equality])
  | .pi first second => .pi first.toCertificate second.toCertificate
  | .sigma first second => .sigma first.toCertificate second.toCertificate
  | .id carrier left right => .id carrier.toCertificate left.toCertificate right.toCertificate
  | .lam body => .lam body.toCertificate
  | .app function argument => .app function.toCertificate argument.toCertificate
  | .pair first second => .pair first.toCertificate second.toCertificate
  | .fst inner => .fst inner.toCertificate
  | .snd inner => .snd inner.toCertificate
  | .refl term => .reflTerm term.toCertificate
  | @Receipt.betaPi _ _ body' _ argument' body argument =>
      (body.toCertificate.lam.app argument.toCertificate).trans
        (.single (.betaPi body' argument') (decide_eq_true rfl))
  | @Receipt.betaSigmaFst _ _ first' _ second' first second =>
      (first.toCertificate.pair second.toCertificate).fst.trans
        (.single (.betaSigmaFst first' second') (decide_eq_true rfl))
  | @Receipt.betaSigmaSnd _ _ first' _ second' first second =>
      (first.toCertificate.pair second.toCertificate).snd.trans
        (.single (.betaSigmaSnd first' second') (decide_eq_true rfl))
  | .listNil ca _a _p z _s => (NativeCompletedRootCertificate.listNil ca).trans z.toCertificate
  | .listCons ca a p z s h t => (NativeCompletedRootCertificate.listCons ca).trans
      (((s.toCertificate.app h.toCertificate).app t.toCertificate).app
        (listElim a.toCertificate p.toCertificate z.toCertificate s.toCertificate t.toCertificate))
  | .identity cy cw _a _x _p d _y _witness => (NativeCompletedRootCertificate.identity cy cw).trans d.toCertificate
  | .relNil ca cb cr cx cy _a _b _r _p z _s _xs _ys => (NativeCompletedRootCertificate.relNil ca cb cr cx cy).trans z.toCertificate
  | .relCons ca cb cr cx cy a b r p z s _xs _ys h k t u he te => (NativeCompletedRootCertificate.relCons ca cb cr cx cy).trans
      (((((((s.toCertificate.app h.toCertificate).app k.toCertificate).app t.toCertificate).app
        u.toCertificate).app he.toCertificate).app te.toCertificate).app
          (relElim a.toCertificate b.toCertificate r.toCertificate p.toCertificate z.toCertificate
            s.toCertificate t.toCertificate u.toCertificate te.toCertificate))

end Receipt

private theorem certificate_nonempty {n : Nat} {left right : Tower.Tm n}
    (conversion : AuthoredConv left right) : Nonempty (Certificate left right) := by
  obtain ⟨code, checked⟩ := NativeRelatorConversionChecking.conversion_iff_checked.mp conversion
  exact ⟨⟨code, checked⟩⟩

/-- Support completeness is a proposition, not an extraction algorithm.
Executable consumers supply receipts with their finite guard certificates. -/
theorem nonempty_of_support {n : Nat} {source target : Tower.Tm n}
    (parallel : NativeRelatorConversionParallel.Par source target) :
    Nonempty (Receipt source target) := by
  induction parallel with
  | var index => exact ⟨.var index⟩
  | const name => exact ⟨.const name⟩
  | head value => exact ⟨.head value⟩
  | headRel equality => exact ⟨.headRel equality⟩
  | pi _ _ h0 h1 =>
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      exact ⟨.pi h0 h1⟩
  | sigma _ _ h0 h1 =>
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      exact ⟨.sigma h0 h1⟩
  | id _ _ _ h0 h1 h2 =>
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      obtain ⟨h2⟩ := h2
      exact ⟨.id h0 h1 h2⟩
  | lam _ h0 =>
      obtain ⟨h0⟩ := h0
      exact ⟨.lam h0⟩
  | app _ _ h0 h1 =>
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      exact ⟨.app h0 h1⟩
  | pair _ _ h0 h1 =>
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      exact ⟨.pair h0 h1⟩
  | fst _ h0 =>
      obtain ⟨h0⟩ := h0
      exact ⟨.fst h0⟩
  | snd _ h0 =>
      obtain ⟨h0⟩ := h0
      exact ⟨.snd h0⟩
  | refl _ h0 =>
      obtain ⟨h0⟩ := h0
      exact ⟨.refl h0⟩
  | betaPi _ _ h0 h1 =>
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      exact ⟨.betaPi h0 h1⟩
  | betaSigmaFst _ _ h0 h1 =>
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      exact ⟨.betaSigmaFst h0 h1⟩
  | betaSigmaSnd _ _ h0 h1 =>
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      exact ⟨.betaSigmaSnd h0 h1⟩
  | listNil g0 _ _ _ _ h0 h1 h2 h3 =>
      obtain ⟨g0⟩ := certificate_nonempty g0
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      obtain ⟨h2⟩ := h2
      obtain ⟨h3⟩ := h3
      exact ⟨.listNil g0 h0 h1 h2 h3⟩
  | listCons g0 _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 =>
      obtain ⟨g0⟩ := certificate_nonempty g0
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      obtain ⟨h2⟩ := h2
      obtain ⟨h3⟩ := h3
      obtain ⟨h4⟩ := h4
      obtain ⟨h5⟩ := h5
      exact ⟨.listCons g0 h0 h1 h2 h3 h4 h5⟩
  | identity g0 g1 _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 =>
      obtain ⟨g0⟩ := certificate_nonempty g0
      obtain ⟨g1⟩ := certificate_nonempty g1
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      obtain ⟨h2⟩ := h2
      obtain ⟨h3⟩ := h3
      obtain ⟨h4⟩ := h4
      obtain ⟨h5⟩ := h5
      exact ⟨.identity g0 g1 h0 h1 h2 h3 h4 h5⟩
  | relNil g0 g1 g2 g3 g4 _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 h7 =>
      obtain ⟨g0⟩ := certificate_nonempty g0
      obtain ⟨g1⟩ := certificate_nonempty g1
      obtain ⟨g2⟩ := certificate_nonempty g2
      obtain ⟨g3⟩ := certificate_nonempty g3
      obtain ⟨g4⟩ := certificate_nonempty g4
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      obtain ⟨h2⟩ := h2
      obtain ⟨h3⟩ := h3
      obtain ⟨h4⟩ := h4
      obtain ⟨h5⟩ := h5
      obtain ⟨h6⟩ := h6
      obtain ⟨h7⟩ := h7
      exact ⟨.relNil g0 g1 g2 g3 g4 h0 h1 h2 h3 h4 h5 h6 h7⟩
  | relCons g0 g1 g2 g3 g4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
      obtain ⟨g0⟩ := certificate_nonempty g0
      obtain ⟨g1⟩ := certificate_nonempty g1
      obtain ⟨g2⟩ := certificate_nonempty g2
      obtain ⟨g3⟩ := certificate_nonempty g3
      obtain ⟨g4⟩ := certificate_nonempty g4
      obtain ⟨h0⟩ := h0
      obtain ⟨h1⟩ := h1
      obtain ⟨h2⟩ := h2
      obtain ⟨h3⟩ := h3
      obtain ⟨h4⟩ := h4
      obtain ⟨h5⟩ := h5
      obtain ⟨h6⟩ := h6
      obtain ⟨h7⟩ := h7
      obtain ⟨h8⟩ := h8
      obtain ⟨h9⟩ := h9
      obtain ⟨h10⟩ := h10
      obtain ⟨h11⟩ := h11
      obtain ⟨h12⟩ := h12
      obtain ⟨h13⟩ := h13
      exact ⟨.relCons g0 g1 g2 g3 g4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13⟩

theorem support_iff_nonempty {n : Nat} {source target : Tower.Tm n} :
    NativeRelatorConversionParallel.Par source target ↔ Nonempty (Receipt source target) :=
  ⟨nonempty_of_support, fun ⟨receipt⟩ => receipt.support⟩

#print axioms Receipt.support
#print axioms Receipt.toCertificate
#print axioms support_iff_nonempty

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt
