import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptInversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptSubstitution
import Mettapedia.Logic.Relation.PathConfluence

/-!
# Computed joins of native parallel receipts

A local join retains the computed common term and both continuation receipts.
Native contraction guards are transported using their supplied finite
certificates and the argument developments, rather than decided anew.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt

open Presentation NativeIndexedFamilies NativeCompletedRootCertificate
open NativeRelatorConversionParallel (listPrefix identityPrefix relPrefix)

variable {n : Nat}

/-- A type tag selecting retained parallel evidence as the graph's arrows. -/
def ReceiptGraph (n : Nat) := Tower.Tm n

instance (n : Nat) : DecidableEq (ReceiptGraph n) :=
  inferInstanceAs (DecidableEq (Tower.Tm n))

instance receiptGraphQuiver (n : Nat) : Quiver (ReceiptGraph n) where
  Hom left right := Receipt left right

abbrev LocalJoin (left right : Tower.Tm n) :=
  Mettapedia.Logic.Relation.PathConfluence.Diamond (V := ReceiptGraph n) left right

abbrev Joins (source : Tower.Tm n) :=
  {left right : Tower.Tm n} → Receipt source left → Receipt source right → LocalJoin left right

def joinListNil
    {a p z s innerA a' p' z' s' target : Tower.Tm n}
    (ca : Certificate innerA a) (function : Joins (listPrefix a p z s))
    (ha : Receipt a a') (hp : Receipt p p') (hz : Receipt z z') (hs : Receipt s s')
    (other : Receipt (Intrinsic.eliminateApp a p z s (Intrinsic.nilApp innerA)) target) :
    LocalJoin z' target := by
  cases other with
  | app functionStep argumentStep =>
      obtain ⟨ar, pr, zr, sr, ⟨rfl⟩, ra, rp, rz, rs⟩ := listPrefixView functionStep
      obtain ⟨ir, ⟨rfl⟩, ri⟩ := nilView argumentStep
      obtain ⟨common, jl, jr⟩ := function (.listPrefixCong ha hp hz hs) functionStep
      obtain ⟨ac, pc, zc, sc, ⟨rfl⟩, la, lp, lz, ls⟩ := listPrefixView jl
      obtain ⟨da, dp, dz, ds⟩ := listPrefixToFixed jr
      exact ⟨zc, lz, .listNil (ca.transport ri.toCertificate ra.toCertificate) da dp dz ds⟩
  | listNil _ ra rp rz rs =>
      obtain ⟨common, jl, jr⟩ := function (.listPrefixCong ha hp hz hs) (.listPrefixCong ra rp rz rs)
      obtain ⟨ac, pc, zc, sc, ⟨rfl⟩, la, lp, lz, ls⟩ := listPrefixView jl
      obtain ⟨da, dp, dz, ds⟩ := listPrefixToFixed jr
      exact ⟨zc, lz, dz⟩


def joinIdentity
    {a x p d y witness a' x' p' d' y' witness' target : Tower.Tm n}
    (cy : Certificate y x) (cw : Certificate witness x)
    (function : Joins (identityPrefix a x p d y))
    (ha : Receipt a a') (hx : Receipt x x') (hp : Receipt p p') (hd : Receipt d d')
    (hy : Receipt y y') (_hw : Receipt witness witness')
    (other : Receipt (Intrinsic.identityEliminateApp a x p d y (.refl witness)) target) :
    LocalJoin d' target := by
  cases other with
  | app functionStep argumentStep =>
      obtain ⟨ar, xr, pr, dr, yr, ⟨rfl⟩, ra, rx, rp, rd, ry⟩ := identityPrefixView functionStep
      obtain ⟨wr, ⟨rfl⟩, rw⟩ := reflView argumentStep
      obtain ⟨common, jl, jr⟩ := function (.identityPrefixCong ha hx hp hd hy) functionStep
      obtain ⟨ac, xc, pc, dc, yc, ⟨rfl⟩, la, lx, lp, ld, ly⟩ := identityPrefixView jl
      obtain ⟨da, dx, dp, dd, dy⟩ := identityPrefixToFixed jr
      exact ⟨dc, ld, .identity
        (cy.transport ry.toCertificate rx.toCertificate)
        (cw.transport rw.toCertificate rx.toCertificate)
        da dx dp dd dy (Receipt.reflexive wr)⟩
  | identity _ _ ra rx rp rd ry _ =>
      obtain ⟨common, jl, jr⟩ := function (.identityPrefixCong ha hx hp hd hy)
        (.identityPrefixCong ra rx rp rd ry)
      obtain ⟨ac, xc, pc, dc, yc, ⟨rfl⟩, la, lx, lp, ld, ly⟩ := identityPrefixView jl
      obtain ⟨da, dx, dp, dd, dy⟩ := identityPrefixToFixed jr
      exact ⟨dc, ld, dd⟩

def joinRelNil
    {a b r p z s xs ys innerA innerB innerR a' b' r' p' z' s' xs' ys' target : Tower.Tm n}
    (ca : Certificate innerA a) (cb : Certificate innerB b) (cr : Certificate innerR r)
    (cx : Certificate xs (Intrinsic.nilApp a)) (cy : Certificate ys (Intrinsic.nilApp b))
    (function : Joins (relPrefix a b r p z s xs ys))
    (ha : Receipt a a') (hb : Receipt b b') (hr : Receipt r r') (hp : Receipt p p')
    (hz : Receipt z z') (hs : Receipt s s') (hx : Receipt xs xs') (hy : Receipt ys ys')
    (other : Receipt (IntrinsicRelator.eliminateApp a b r p z s xs ys
      (IntrinsicRelator.nilRelApp innerA innerB innerR)) target) :
    LocalJoin z' target := by
  cases other with
  | app functionStep argumentStep =>
      obtain ⟨ar, br, rr, pr, zr, sr, xr, yr, ⟨rfl⟩, ra, rb, rrel, rp, rz, rs, rx, ry⟩ :=
        relPrefixView functionStep
      obtain ⟨irA, irB, irR, ⟨rfl⟩, riA, riB, riR⟩ := nilRelView argumentStep
      obtain ⟨common, jl, jr⟩ := function (.relPrefixCong ha hb hr hp hz hs hx hy) functionStep
      obtain ⟨ac, bc, rc, pc, zc, sc, xc, yc, ⟨rfl⟩, la, lb, lr, lp, lz, ls, lx, ly⟩ :=
        relPrefixView jl
      obtain ⟨da, db, dr, dp, dz, ds, dx, dy⟩ := relPrefixToFixed jr
      exact ⟨zc, lz, .relNil
        (ca.transport riA.toCertificate ra.toCertificate)
        (cb.transport riB.toCertificate rb.toCertificate)
        (cr.transport riR.toCertificate rrel.toCertificate)
        (cx.transport rx.toCertificate (nilApp ra.toCertificate))
        (cy.transport ry.toCertificate (nilApp rb.toCertificate))
        da db dr dp dz ds dx dy⟩
  | relNil _ _ _ _ _ ra rb rr rp rz rs rx ry =>
      obtain ⟨common, jl, jr⟩ := function (.relPrefixCong ha hb hr hp hz hs hx hy)
        (.relPrefixCong ra rb rr rp rz rs rx ry)
      obtain ⟨ac, bc, rc, pc, zc, sc, xc, yc, ⟨rfl⟩, la, lb, lr, lp, lz, ls, lx, ly⟩ :=
        relPrefixView jl
      obtain ⟨da, db, dr, dp, dz, ds, dx, dy⟩ := relPrefixToFixed jr
      exact ⟨zc, lz, dz⟩

def joinListCons
    {a p z s innerA h t a' p' z' s' h' t' target : Tower.Tm n}
    (ca : Certificate innerA a)
    (function : Joins (listPrefix a p z s))
    (argument : Joins (Intrinsic.consApp innerA h t))
    (ha : Receipt a a') (hp : Receipt p p') (hz : Receipt z z') (hs : Receipt s s') (hh : Receipt h h') (ht : Receipt t t')
    (other : Receipt (Intrinsic.eliminateApp a p z s (Intrinsic.consApp innerA h t)) target) :
    LocalJoin (.app (.app (.app s' h') t') (Intrinsic.eliminateApp a' p' z' s' t')) target := by
  cases other with
  | app functionStep argumentStep =>
      obtain ⟨ar, pr, zr, sr, ⟨rfl⟩, ra, rp, rz, rs⟩ :=
        listPrefixView functionStep
      obtain ⟨innerAr, hr, tr, ⟨rfl⟩, rinnerA, rh, rt⟩ :=
        consView argumentStep
      obtain ⟨commonF, jl, jr⟩ := function (.listPrefixCong ha hp hz hs) functionStep
      obtain ⟨ac, pc, zc, sc, ⟨rfl⟩, la, lp, lz, ls⟩ := listPrefixView jl
      obtain ⟨da, dp, dz, ds⟩ := listPrefixToFixed jr
      obtain ⟨commonA, al, ar⟩ := argument
        (.consCong (Receipt.reflexive innerA) hh ht) argumentStep
      obtain ⟨innerAc, hc, tc, ⟨rfl⟩, linnerA, lh, lt⟩ := consView al
      obtain ⟨dinnerA, dh, dt⟩ := consToFixed ar
      exact ⟨_, .app (.app (.app ls lh) lt) (.app (.listPrefixCong la lp lz ls) lt), .listCons
        (ca.transport rinnerA.toCertificate ra.toCertificate)
        da dp dz ds dh dt⟩
  | listCons _ ra rp rz rs rh rt =>
      obtain ⟨commonF, jl, jr⟩ := function (.listPrefixCong ha hp hz hs)
        (.listPrefixCong ra rp rz rs)
      obtain ⟨ac, pc, zc, sc, ⟨rfl⟩, la, lp, lz, ls⟩ := listPrefixView jl
      obtain ⟨da, dp, dz, ds⟩ := listPrefixToFixed jr
      obtain ⟨commonA, al, ar⟩ := argument
        (.consCong (Receipt.reflexive innerA) hh ht)
        (.consCong (Receipt.reflexive innerA) rh rt)
      obtain ⟨innerAc, hc, tc, ⟨rfl⟩, linnerA, lh, lt⟩ := consView al
      obtain ⟨dinnerA, dh, dt⟩ := consToFixed ar
      exact ⟨_, .app (.app (.app ls lh) lt) (.app (.listPrefixCong la lp lz ls) lt), .app (.app (.app ds dh) dt) (.app (.listPrefixCong da dp dz ds) dt)⟩

def joinRelCons
    {a b r p z s xs ys innerA innerB innerR h k t u he te a' b' r' p' z' s' xs' ys' h' k' t' u' he' te' target : Tower.Tm n}
    (ca : Certificate innerA a) (cb : Certificate innerB b) (cr : Certificate innerR r)
    (cx : Certificate xs (Intrinsic.consApp a h t)) (cy : Certificate ys (Intrinsic.consApp b k u))
    (function : Joins (relPrefix a b r p z s xs ys))
    (argument : Joins (IntrinsicRelator.consRelApp innerA innerB innerR h k t u he te))
    (ha : Receipt a a') (hb : Receipt b b') (hr : Receipt r r') (hp : Receipt p p') (hz : Receipt z z') (hs : Receipt s s') (hxs : Receipt xs xs') (hys : Receipt ys ys') (hh : Receipt h h') (hk : Receipt k k') (ht : Receipt t t') (hu : Receipt u u') (hhe : Receipt he he') (hte : Receipt te te')
    (other : Receipt (IntrinsicRelator.eliminateApp a b r p z s xs ys (IntrinsicRelator.consRelApp innerA innerB innerR h k t u he te)) target) :
    LocalJoin (.app (.app (.app (.app (.app (.app (.app s' h') k') t') u') he') te') (IntrinsicRelator.eliminateApp a' b' r' p' z' s' t' u' te')) target := by
  cases other with
  | app functionStep argumentStep =>
      obtain ⟨ar, br, rr, pr, zr, sr, xsr, ysr, ⟨rfl⟩, ra, rb, rr, rp, rz, rs, rxs, rys⟩ :=
        relPrefixView functionStep
      obtain ⟨innerAr, innerBr, innerRr, headRight, kr, tr, ur, her, ter, ⟨rfl⟩, rinnerA, rinnerB, rinnerR, rh, rk, rt, ru, rhe, rte⟩ :=
        consRelView argumentStep
      obtain ⟨commonF, jl, jr⟩ := function (.relPrefixCong ha hb hr hp hz hs hxs hys) functionStep
      obtain ⟨ac, bc, rc, pc, zc, sc, xsc, ysc, ⟨rfl⟩, la, lb, lr, lp, lz, ls, lxs, lys⟩ := relPrefixView jl
      obtain ⟨da, db, dr, dp, dz, ds, dxs, dys⟩ := relPrefixToFixed jr
      obtain ⟨commonA, al, ar⟩ := argument
        (.consRelCong (Receipt.reflexive innerA) (Receipt.reflexive innerB) (Receipt.reflexive innerR) hh hk ht hu hhe hte) argumentStep
      obtain ⟨innerAc, innerBc, innerRc, hc, kc, tc, uc, hec, tec, ⟨rfl⟩, linnerA, linnerB, linnerR, lh, lk, lt, lu, lhe, lte⟩ := consRelView al
      obtain ⟨dinnerA, dinnerB, dinnerR, dh, dk, dt, du, dhe, dte⟩ := consRelToFixed ar
      exact ⟨_, .app (.app (.app (.app (.app (.app (.app ls lh) lk) lt) lu) lhe) lte) (.app (.relPrefixCong la lb lr lp lz ls lt lu) lte), .relCons
        (ca.transport rinnerA.toCertificate ra.toCertificate)
        (cb.transport rinnerB.toCertificate rb.toCertificate)
        (cr.transport rinnerR.toCertificate rr.toCertificate)
        (cx.transport rxs.toCertificate (consApp ra.toCertificate rh.toCertificate rt.toCertificate))
        (cy.transport rys.toCertificate (consApp rb.toCertificate rk.toCertificate ru.toCertificate))
        da db dr dp dz ds dxs dys dh dk dt du dhe dte⟩
  | relCons _ _ _ _ _ ra rb rr rp rz rs rxs rys rh rk rt ru rhe rte =>
      obtain ⟨commonF, jl, jr⟩ := function (.relPrefixCong ha hb hr hp hz hs hxs hys)
        (.relPrefixCong ra rb rr rp rz rs rxs rys)
      obtain ⟨ac, bc, rc, pc, zc, sc, xsc, ysc, ⟨rfl⟩, la, lb, lr, lp, lz, ls, lxs, lys⟩ := relPrefixView jl
      obtain ⟨da, db, dr, dp, dz, ds, dxs, dys⟩ := relPrefixToFixed jr
      obtain ⟨commonA, al, ar⟩ := argument
        (.consRelCong (Receipt.reflexive innerA) (Receipt.reflexive innerB) (Receipt.reflexive innerR) hh hk ht hu hhe hte)
        (.consRelCong (Receipt.reflexive innerA) (Receipt.reflexive innerB) (Receipt.reflexive innerR) rh rk rt ru rhe rte)
      obtain ⟨innerAc, innerBc, innerRc, hc, kc, tc, uc, hec, tec, ⟨rfl⟩, linnerA, linnerB, linnerR, lh, lk, lt, lu, lhe, lte⟩ := consRelView al
      obtain ⟨dinnerA, dinnerB, dinnerR, dh, dk, dt, du, dhe, dte⟩ := consRelToFixed ar
      exact ⟨_, .app (.app (.app (.app (.app (.app (.app ls lh) lk) lt) lu) lhe) lte) (.app (.relPrefixCong la lb lr lp lz ls lt lu) lte), .app (.app (.app (.app (.app (.app (.app ds dh) dk) dt) du) dhe) dte) (.app (.relPrefixCong da db dr dp dz ds dt du) dte)⟩


def joinBeta
    {body body' : Tower.Tm (n + 1)} {argument argument' target : Tower.Tm n}
    (functionJoin : Joins (.lam body)) (argumentJoin : Joins argument)
    (bodyStep : Receipt body body') (argumentStep : Receipt argument argument')
    (other : Receipt (.app (.lam body) argument) target) :
    LocalJoin (inst0 argument' body') target := by
  cases other with
  | app rightFunction rightArgument =>
      obtain ⟨br, ⟨rfl⟩, rb⟩ := lamView rightFunction
      obtain ⟨commonF, jl, jr⟩ := functionJoin (.lam bodyStep) rightFunction
      obtain ⟨bc, ⟨rfl⟩, lb⟩ := lamView jl
      have db := lamToFixed jr
      obtain ⟨ac, la, da⟩ := argumentJoin argumentStep rightArgument
      exact ⟨inst0 ac bc, instantiateReceipt la lb, .betaPi db da⟩
  | betaPi rightBody rightArgument =>
      obtain ⟨commonF, jl, jr⟩ := functionJoin (.lam bodyStep) (.lam rightBody)
      obtain ⟨bc, ⟨rfl⟩, lb⟩ := lamView jl
      have db := lamToFixed jr
      obtain ⟨ac, la, da⟩ := argumentJoin argumentStep rightArgument
      exact ⟨inst0 ac bc, instantiateReceipt la lb, instantiateReceipt da db⟩

def joinPairFst
    {first second first' second' target : Tower.Tm n}
    (innerJoin : Joins (.pair first second))
    (left : Receipt first first') (right : Receipt second second')
    (other : Receipt (.fst (.pair first second)) target) :
    LocalJoin first' target := by
  cases other with
  | fst inner =>
      obtain ⟨fr, sr, ⟨rfl⟩, rf, rs⟩ := pairView inner
      obtain ⟨common, jl, jr⟩ := innerJoin (.pair left right) inner
      obtain ⟨fc, sc, ⟨rfl⟩, lf, ls⟩ := pairView jl
      obtain ⟨df, ds⟩ := pairToFixed jr
      exact ⟨fc, lf, .betaSigmaFst df ds⟩
  | betaSigmaFst rf rs =>
      obtain ⟨common, jl, jr⟩ := innerJoin (.pair left right) (.pair rf rs)
      obtain ⟨fc, sc, ⟨rfl⟩, lf, ls⟩ := pairView jl
      obtain ⟨df, ds⟩ := pairToFixed jr
      exact ⟨fc, lf, df⟩

def joinPairSnd
    {first second first' second' target : Tower.Tm n}
    (innerJoin : Joins (.pair first second))
    (left : Receipt first first') (right : Receipt second second')
    (other : Receipt (.snd (.pair first second)) target) :
    LocalJoin second' target := by
  cases other with
  | snd inner =>
      obtain ⟨fr, sr, ⟨rfl⟩, rf, rs⟩ := pairView inner
      obtain ⟨common, jl, jr⟩ := innerJoin (.pair left right) inner
      obtain ⟨fc, sc, ⟨rfl⟩, lf, ls⟩ := pairView jl
      obtain ⟨df, ds⟩ := pairToFixed jr
      exact ⟨sc, ls, .betaSigmaSnd df ds⟩
  | betaSigmaSnd rf rs =>
      obtain ⟨common, jl, jr⟩ := innerJoin (.pair left right) (.pair rf rs)
      obtain ⟨fc, sc, ⟨rfl⟩, lf, ls⟩ := pairView jl
      obtain ⟨df, ds⟩ := pairToFixed jr
      exact ⟨sc, ls, ds⟩

def joinApp {function argument left right : Tower.Tm n}
    (functionJoin : Joins function) (argumentJoin : Joins argument)
    (first : Receipt (.app function argument) left)
    (second : Receipt (.app function argument) right) : LocalJoin left right := by
  cases first with
  | app lf la =>
      cases second with
      | app rf ra =>
          obtain ⟨fc, fl, fr⟩ := functionJoin lf rf
          obtain ⟨ac, al, ar⟩ := argumentJoin la ra
          exact ⟨.app fc ac, .app fl al, .app fr ar⟩
      | betaPi rb ra => exact (joinBeta functionJoin argumentJoin rb ra (.app lf la)).symm
      | listNil ca a p z s => exact (joinListNil ca functionJoin a p z s (.app lf la)).symm
      | listCons ca a p z s h t =>
          exact (joinListCons ca functionJoin argumentJoin a p z s h t (.app lf la)).symm
      | identity cy cw a x p d y w =>
          exact (joinIdentity cy cw functionJoin a x p d y w (.app lf la)).symm
      | relNil ca cb cr cx cy a b r p z s xs ys =>
          exact (joinRelNil ca cb cr cx cy functionJoin a b r p z s xs ys (.app lf la)).symm
      | relCons ca cb cr cx cy a b r p z s xs ys h k t u he te =>
          exact (joinRelCons ca cb cr cx cy functionJoin argumentJoin
            a b r p z s xs ys h k t u he te (.app lf la)).symm
  | betaPi lb la => exact joinBeta functionJoin argumentJoin lb la second
  | listNil ca a p z s => exact joinListNil ca functionJoin a p z s second
  | listCons ca a p z s h t => exact joinListCons ca functionJoin argumentJoin a p z s h t second
  | identity cy cw a x p d y w => exact joinIdentity cy cw functionJoin a x p d y w second
  | relNil ca cb cr cx cy a b r p z s xs ys =>
      exact joinRelNil ca cb cr cx cy functionJoin a b r p z s xs ys second
  | relCons ca cb cr cx cy a b r p z s xs ys h k t u he te =>
      exact joinRelCons ca cb cr cx cy functionJoin argumentJoin a b r p z s xs ys h k t u he te second

def joinFst {inner left right : Tower.Tm n} (innerJoin : Joins inner)
    (first : Receipt (.fst inner) left) (second : Receipt (.fst inner) right) :
    LocalJoin left right := by
  cases first with
  | fst leftStep =>
      cases second with
      | fst rightStep =>
          obtain ⟨common, jl, jr⟩ := innerJoin leftStep rightStep
          exact ⟨.fst common, .fst jl, .fst jr⟩
      | betaSigmaFst rf rs => exact (joinPairFst innerJoin rf rs (.fst leftStep)).symm
  | betaSigmaFst lf ls => exact joinPairFst innerJoin lf ls second

def joinSnd {inner left right : Tower.Tm n} (innerJoin : Joins inner)
    (first : Receipt (.snd inner) left) (second : Receipt (.snd inner) right) :
    LocalJoin left right := by
  cases first with
  | snd leftStep =>
      cases second with
      | snd rightStep =>
          obtain ⟨common, jl, jr⟩ := innerJoin leftStep rightStep
          exact ⟨.snd common, .snd jl, .snd jr⟩
      | betaSigmaSnd rf rs => exact (joinPairSnd innerJoin rf rs (.snd leftStep)).symm
  | betaSigmaSnd lf ls => exact joinPairSnd innerJoin lf ls second

private def reverseHead {value : Tower.Head} {target : Tower.Tm n}
    (receipt : Receipt (.head value) target) : Receipt target (.head value) := by
  cases receipt with
  | head _ => exact .head _
  | headRel equality => exact .headRel (LevelTower.headEq_symmetric.symm _ _ equality)

/-- Compute a native parallel diamond from the two selected finite derivations.
Recursion is on the common source syntax; conversion guards are never searched. -/
def localJoin {n : Nat} (source : Tower.Tm n) : Joins source := by
  match source with
  | .var index =>
      intro left right first second
      cases first
      cases second
      exact ⟨.var index, .var index, .var index⟩
  | .const name =>
      intro left right first second
      cases first
      cases second
      exact ⟨.const name, .const name, .const name⟩
  | .head value =>
      intro left right first second
      exact ⟨.head value, reverseHead first, reverseHead second⟩
  | .pi domain codomain =>
      let domainJoin : Joins domain := localJoin domain
      let codomainJoin : Joins codomain := localJoin codomain
      intro left right first second
      cases first with | pi ld lc =>
        cases second with | pi rd rc =>
          obtain ⟨dc, dl, dr⟩ := domainJoin ld rd
          obtain ⟨cc, cl, cr⟩ := codomainJoin lc rc
          exact ⟨.pi dc cc, .pi dl cl, .pi dr cr⟩
  | .sigma domain codomain =>
      let domainJoin : Joins domain := localJoin domain
      let codomainJoin : Joins codomain := localJoin codomain
      intro left right first second
      cases first with | sigma ld lc =>
        cases second with | sigma rd rc =>
          obtain ⟨dc, dl, dr⟩ := domainJoin ld rd
          obtain ⟨cc, cl, cr⟩ := codomainJoin lc rc
          exact ⟨.sigma dc cc, .sigma dl cl, .sigma dr cr⟩
  | .id carrier left right =>
      let carrierJoin : Joins carrier := localJoin carrier
      let leftJoin : Joins left := localJoin left
      let rightJoin : Joins right := localJoin right
      intro targetLeft targetRight first second
      cases first with | id lc ll lr =>
        cases second with | id rc rl rr =>
          obtain ⟨cc, cl, cr⟩ := carrierJoin lc rc
          obtain ⟨llc, lll, llr⟩ := leftJoin ll rl
          obtain ⟨rrc, rrl, rrr⟩ := rightJoin lr rr
          exact ⟨.id cc llc rrc, .id cl lll rrl, .id cr llr rrr⟩
  | .lam body =>
      let bodyJoin : Joins body := localJoin body
      intro left right first second
      cases first with | lam lb =>
        cases second with | lam rb =>
          obtain ⟨bc, bl, br⟩ := bodyJoin lb rb
          exact ⟨.lam bc, .lam bl, .lam br⟩
  | .app function argument =>
      intro left right first second
      exact joinApp (localJoin function) (localJoin argument) first second
  | .pair first second =>
      let firstJoin : Joins first := localJoin first
      let secondJoin : Joins second := localJoin second
      intro left right firstStep secondStep
      cases firstStep with | pair lf ls =>
        cases secondStep with | pair rf rs =>
          obtain ⟨fc, fl, fr⟩ := firstJoin lf rf
          obtain ⟨sc, sl, sr⟩ := secondJoin ls rs
          exact ⟨.pair fc sc, .pair fl sl, .pair fr sr⟩
  | .fst inner =>
      intro left right first second
      exact joinFst (localJoin inner) first second
  | .snd inner =>
      intro left right first second
      exact joinSnd (localJoin inner) first second
  | .refl term =>
      let termJoin : Joins term := localJoin term
      intro left right first second
      cases first with | refl leftStep =>
        cases second with | refl rightStep =>
          obtain ⟨common, jl, jr⟩ := termJoin leftStep rightStep
          exact ⟨.refl common, .refl jl, .refl jr⟩

#print axioms localJoin
#print axioms joinListNil
#print axioms joinListCons
#print axioms joinIdentity
#print axioms joinRelNil
#print axioms joinRelCons

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt
