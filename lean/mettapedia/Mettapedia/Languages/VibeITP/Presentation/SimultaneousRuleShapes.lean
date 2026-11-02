import Mettapedia.Languages.VibeITP.Presentation.SimultaneousRules
import Mettapedia.Languages.VibeITP.Presentation.Instances

/-! Exact v2 rule-instance shapes, generated from the actual schemas by
`scripts/generate_vibe_itp_simultaneous_shapes.py`. These are structural
instantiation and introduction laws, not specification soundness proofs. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.FirstOrderRules

theorem inst_rManyPrepareNil  :
    rManyPrepareNil.instPremises [] = [] ∧
      rManyPrepareNil.instConclusion [] = (jManyPrepare cNil cNil) := by
  simp [rManyPrepareNil, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, cNil, jManyPrepare]

theorem sound_rManyPrepareNil {P : Pattern → Prop}
    (sound : P (jManyPrepare cNil cNil)) :
    ∀ args : List Pattern, args.length = rManyPrepareNil.vars.length →
      (∀ premise ∈ rManyPrepareNil.instPremises args, P premise) → P (rManyPrepareNil.instConclusion args) := by
  intro args length premises
  match args, length with
  | [], _ =>
      rw [(inst_rManyPrepareNil ).1] at premises
      rw [(inst_rManyPrepareNil ).2]
      exact sound  

theorem intro_rManyPrepareNil {R : List FORule} (member : rManyPrepareNil ∈ R) 
      : FODerivable R (jManyPrepare cNil cNil) := by
  apply FODerivable.intro member [] rfl
  · intro argument included
    simp only [List.not_mem_nil] at included
  · exact (inst_rManyPrepareNil ).2
  · rw [(inst_rManyPrepareNil ).1]
    intro goal included
    simp only [List.not_mem_nil] at included

theorem inst_rManyPrepareCons (fid fbs v n d reps entries : Pattern) :
    rManyPrepareCons.instPremises [fid, fbs, v, n, d, reps, entries] = [jSymDecl (cSym fid cKFvar fbs), jLen fbs n, jWf v, jDepth v d, jNLe d n, jManyPrepare reps entries] ∧
      rManyPrepareCons.instConclusion [fid, fbs, v, n, d, reps, entries] = (jManyPrepare (cCons (pairPattern (cSym fid cKFvar fbs) v) reps) (cCons (entryPattern (cSym fid cKFvar fbs) n v) entries)) := by
  simp [rManyPrepareCons, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cCons, cKFvar, cNil, cSym, entryPattern, fvarSym, jDepth, jLen, jManyPrepare, jNLe, jSymDecl, jWf, pairPattern]

theorem sound_rManyPrepareCons {P : Pattern → Prop}
    (sound : ∀ fid fbs v n d reps entries : Pattern, P (jSymDecl (cSym fid cKFvar fbs)) → P (jLen fbs n) → P (jWf v) → P (jDepth v d) → P (jNLe d n) → P (jManyPrepare reps entries) → P (jManyPrepare (cCons (pairPattern (cSym fid cKFvar fbs) v) reps) (cCons (entryPattern (cSym fid cKFvar fbs) n v) entries))) :
    ∀ args : List Pattern, args.length = rManyPrepareCons.vars.length →
      (∀ premise ∈ rManyPrepareCons.instPremises args, P premise) → P (rManyPrepareCons.instConclusion args) := by
  intro args length premises
  match args, length with
  | [fid, fbs, v, n, d, reps, entries], _ =>
      rw [(inst_rManyPrepareCons fid fbs v n d reps entries).1] at premises
      rw [(inst_rManyPrepareCons fid fbs v n d reps entries).2]
      exact sound fid fbs v n d reps entries (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp))

theorem intro_rManyPrepareCons {R : List FORule} (member : rManyPrepareCons ∈ R) {fid fbs v n d reps entries : Pattern}
    (data_fid : IsData fid) (data_fbs : IsData fbs) (data_v : IsData v) (data_n : IsData n) (data_d : IsData d) (data_reps : IsData reps) (data_entries : IsData entries) (premise0 : FODerivable R (jSymDecl (cSym fid cKFvar fbs))) (premise1 : FODerivable R (jLen fbs n)) (premise2 : FODerivable R (jWf v)) (premise3 : FODerivable R (jDepth v d)) (premise4 : FODerivable R (jNLe d n)) (premise5 : FODerivable R (jManyPrepare reps entries)) : FODerivable R (jManyPrepare (cCons (pairPattern (cSym fid cKFvar fbs) v) reps) (cCons (entryPattern (cSym fid cKFvar fbs) n v) entries)) := by
  apply FODerivable.intro member [fid, fbs, v, n, d, reps, entries] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rManyPrepareCons fid fbs v n d reps entries).2
  · rw [(inst_rManyPrepareCons fid fbs v n d reps entries).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem inst_rManyHitFirst (fid fbs n v rest : Pattern) :
    rManyHitFirst.instPremises [fid, fbs, n, v, rest] = [] ∧
      rManyHitFirst.instConclusion [fid, fbs, n, v, rest] = (jManyHit (cCons (entryPattern (cSym fid cKFvar fbs) n v) rest) (cSym fid cKFvar fbs) n v) := by
  simp [rManyHitFirst, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cCons, cKFvar, cNil, cSym, entryPattern, fvarSym, jManyHit]

theorem sound_rManyHitFirst {P : Pattern → Prop}
    (sound : ∀ fid fbs n v rest : Pattern, P (jManyHit (cCons (entryPattern (cSym fid cKFvar fbs) n v) rest) (cSym fid cKFvar fbs) n v)) :
    ∀ args : List Pattern, args.length = rManyHitFirst.vars.length →
      (∀ premise ∈ rManyHitFirst.instPremises args, P premise) → P (rManyHitFirst.instConclusion args) := by
  intro args length premises
  match args, length with
  | [fid, fbs, n, v, rest], _ =>
      rw [(inst_rManyHitFirst fid fbs n v rest).1] at premises
      rw [(inst_rManyHitFirst fid fbs n v rest).2]
      exact sound fid fbs n v rest 

theorem intro_rManyHitFirst {R : List FORule} (member : rManyHitFirst ∈ R) {fid fbs n v rest : Pattern}
    (data_fid : IsData fid) (data_fbs : IsData fbs) (data_n : IsData n) (data_v : IsData v) (data_rest : IsData rest)  : FODerivable R (jManyHit (cCons (entryPattern (cSym fid cKFvar fbs) n v) rest) (cSym fid cKFvar fbs) n v) := by
  apply FODerivable.intro member [fid, fbs, n, v, rest] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rManyHitFirst fid fbs n v rest).2
  · rw [(inst_rManyHitFirst fid fbs n v rest).1]
    intro goal included
    simp only [List.not_mem_nil] at included

theorem inst_rManyHitLt (idv bs k w rest fid fbs n v : Pattern) :
    rManyHitLt.instPremises [idv, bs, k, w, rest, fid, fbs, n, v] = [jNLt idv fid, jManyHit rest (cSym fid cKFvar fbs) n v] ∧
      rManyHitLt.instConclusion [idv, bs, k, w, rest, fid, fbs, n, v] = (jManyHit (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs) n v) := by
  simp [rManyHitLt, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cCons, cKFvar, cNil, cSym, entryPattern, fvarSym, jManyHit, jNLt]

theorem sound_rManyHitLt {P : Pattern → Prop}
    (sound : ∀ idv bs k w rest fid fbs n v : Pattern, P (jNLt idv fid) → P (jManyHit rest (cSym fid cKFvar fbs) n v) → P (jManyHit (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs) n v)) :
    ∀ args : List Pattern, args.length = rManyHitLt.vars.length →
      (∀ premise ∈ rManyHitLt.instPremises args, P premise) → P (rManyHitLt.instConclusion args) := by
  intro args length premises
  match args, length with
  | [idv, bs, k, w, rest, fid, fbs, n, v], _ =>
      rw [(inst_rManyHitLt idv bs k w rest fid fbs n v).1] at premises
      rw [(inst_rManyHitLt idv bs k w rest fid fbs n v).2]
      exact sound idv bs k w rest fid fbs n v (premises _ (by simp)) (premises _ (by simp))

theorem intro_rManyHitLt {R : List FORule} (member : rManyHitLt ∈ R) {idv bs k w rest fid fbs n v : Pattern}
    (data_idv : IsData idv) (data_bs : IsData bs) (data_k : IsData k) (data_w : IsData w) (data_rest : IsData rest) (data_fid : IsData fid) (data_fbs : IsData fbs) (data_n : IsData n) (data_v : IsData v) (premise0 : FODerivable R (jNLt idv fid)) (premise1 : FODerivable R (jManyHit rest (cSym fid cKFvar fbs) n v)) : FODerivable R (jManyHit (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs) n v) := by
  apply FODerivable.intro member [idv, bs, k, w, rest, fid, fbs, n, v] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rManyHitLt idv bs k w rest fid fbs n v).2
  · rw [(inst_rManyHitLt idv bs k w rest fid fbs n v).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl <;> assumption

theorem inst_rManyHitGt (idv bs k w rest fid fbs n v : Pattern) :
    rManyHitGt.instPremises [idv, bs, k, w, rest, fid, fbs, n, v] = [jNLt fid idv, jManyHit rest (cSym fid cKFvar fbs) n v] ∧
      rManyHitGt.instConclusion [idv, bs, k, w, rest, fid, fbs, n, v] = (jManyHit (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs) n v) := by
  simp [rManyHitGt, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cCons, cKFvar, cNil, cSym, entryPattern, fvarSym, jManyHit, jNLt]

theorem sound_rManyHitGt {P : Pattern → Prop}
    (sound : ∀ idv bs k w rest fid fbs n v : Pattern, P (jNLt fid idv) → P (jManyHit rest (cSym fid cKFvar fbs) n v) → P (jManyHit (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs) n v)) :
    ∀ args : List Pattern, args.length = rManyHitGt.vars.length →
      (∀ premise ∈ rManyHitGt.instPremises args, P premise) → P (rManyHitGt.instConclusion args) := by
  intro args length premises
  match args, length with
  | [idv, bs, k, w, rest, fid, fbs, n, v], _ =>
      rw [(inst_rManyHitGt idv bs k w rest fid fbs n v).1] at premises
      rw [(inst_rManyHitGt idv bs k w rest fid fbs n v).2]
      exact sound idv bs k w rest fid fbs n v (premises _ (by simp)) (premises _ (by simp))

theorem intro_rManyHitGt {R : List FORule} (member : rManyHitGt ∈ R) {idv bs k w rest fid fbs n v : Pattern}
    (data_idv : IsData idv) (data_bs : IsData bs) (data_k : IsData k) (data_w : IsData w) (data_rest : IsData rest) (data_fid : IsData fid) (data_fbs : IsData fbs) (data_n : IsData n) (data_v : IsData v) (premise0 : FODerivable R (jNLt fid idv)) (premise1 : FODerivable R (jManyHit rest (cSym fid cKFvar fbs) n v)) : FODerivable R (jManyHit (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs) n v) := by
  apply FODerivable.intro member [idv, bs, k, w, rest, fid, fbs, n, v] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rManyHitGt idv bs k w rest fid fbs n v).2
  · rw [(inst_rManyHitGt idv bs k w rest fid fbs n v).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl <;> assumption

theorem inst_rManyMissNil (fid fbs : Pattern) :
    rManyMissNil.instPremises [fid, fbs] = [] ∧
      rManyMissNil.instConclusion [fid, fbs] = (jManyMiss cNil (cSym fid cKFvar fbs)) := by
  simp [rManyMissNil, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cKFvar, cNil, cSym, fvarSym, jManyMiss]

theorem sound_rManyMissNil {P : Pattern → Prop}
    (sound : ∀ fid fbs : Pattern, P (jManyMiss cNil (cSym fid cKFvar fbs))) :
    ∀ args : List Pattern, args.length = rManyMissNil.vars.length →
      (∀ premise ∈ rManyMissNil.instPremises args, P premise) → P (rManyMissNil.instConclusion args) := by
  intro args length premises
  match args, length with
  | [fid, fbs], _ =>
      rw [(inst_rManyMissNil fid fbs).1] at premises
      rw [(inst_rManyMissNil fid fbs).2]
      exact sound fid fbs 

theorem intro_rManyMissNil {R : List FORule} (member : rManyMissNil ∈ R) {fid fbs : Pattern}
    (data_fid : IsData fid) (data_fbs : IsData fbs)  : FODerivable R (jManyMiss cNil (cSym fid cKFvar fbs)) := by
  apply FODerivable.intro member [fid, fbs] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl <;> assumption
  · exact (inst_rManyMissNil fid fbs).2
  · rw [(inst_rManyMissNil fid fbs).1]
    intro goal included
    simp only [List.not_mem_nil] at included

theorem inst_rManyMissLt (idv bs k w rest fid fbs : Pattern) :
    rManyMissLt.instPremises [idv, bs, k, w, rest, fid, fbs] = [jNLt idv fid, jManyMiss rest (cSym fid cKFvar fbs)] ∧
      rManyMissLt.instConclusion [idv, bs, k, w, rest, fid, fbs] = (jManyMiss (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs)) := by
  simp [rManyMissLt, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cCons, cKFvar, cNil, cSym, entryPattern, fvarSym, jManyMiss, jNLt]

theorem sound_rManyMissLt {P : Pattern → Prop}
    (sound : ∀ idv bs k w rest fid fbs : Pattern, P (jNLt idv fid) → P (jManyMiss rest (cSym fid cKFvar fbs)) → P (jManyMiss (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs))) :
    ∀ args : List Pattern, args.length = rManyMissLt.vars.length →
      (∀ premise ∈ rManyMissLt.instPremises args, P premise) → P (rManyMissLt.instConclusion args) := by
  intro args length premises
  match args, length with
  | [idv, bs, k, w, rest, fid, fbs], _ =>
      rw [(inst_rManyMissLt idv bs k w rest fid fbs).1] at premises
      rw [(inst_rManyMissLt idv bs k w rest fid fbs).2]
      exact sound idv bs k w rest fid fbs (premises _ (by simp)) (premises _ (by simp))

theorem intro_rManyMissLt {R : List FORule} (member : rManyMissLt ∈ R) {idv bs k w rest fid fbs : Pattern}
    (data_idv : IsData idv) (data_bs : IsData bs) (data_k : IsData k) (data_w : IsData w) (data_rest : IsData rest) (data_fid : IsData fid) (data_fbs : IsData fbs) (premise0 : FODerivable R (jNLt idv fid)) (premise1 : FODerivable R (jManyMiss rest (cSym fid cKFvar fbs))) : FODerivable R (jManyMiss (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs)) := by
  apply FODerivable.intro member [idv, bs, k, w, rest, fid, fbs] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rManyMissLt idv bs k w rest fid fbs).2
  · rw [(inst_rManyMissLt idv bs k w rest fid fbs).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl <;> assumption

theorem inst_rManyMissGt (idv bs k w rest fid fbs : Pattern) :
    rManyMissGt.instPremises [idv, bs, k, w, rest, fid, fbs] = [jNLt fid idv, jManyMiss rest (cSym fid cKFvar fbs)] ∧
      rManyMissGt.instConclusion [idv, bs, k, w, rest, fid, fbs] = (jManyMiss (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs)) := by
  simp [rManyMissGt, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cCons, cKFvar, cNil, cSym, entryPattern, fvarSym, jManyMiss, jNLt]

theorem sound_rManyMissGt {P : Pattern → Prop}
    (sound : ∀ idv bs k w rest fid fbs : Pattern, P (jNLt fid idv) → P (jManyMiss rest (cSym fid cKFvar fbs)) → P (jManyMiss (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs))) :
    ∀ args : List Pattern, args.length = rManyMissGt.vars.length →
      (∀ premise ∈ rManyMissGt.instPremises args, P premise) → P (rManyMissGt.instConclusion args) := by
  intro args length premises
  match args, length with
  | [idv, bs, k, w, rest, fid, fbs], _ =>
      rw [(inst_rManyMissGt idv bs k w rest fid fbs).1] at premises
      rw [(inst_rManyMissGt idv bs k w rest fid fbs).2]
      exact sound idv bs k w rest fid fbs (premises _ (by simp)) (premises _ (by simp))

theorem intro_rManyMissGt {R : List FORule} (member : rManyMissGt ∈ R) {idv bs k w rest fid fbs : Pattern}
    (data_idv : IsData idv) (data_bs : IsData bs) (data_k : IsData k) (data_w : IsData w) (data_rest : IsData rest) (data_fid : IsData fid) (data_fbs : IsData fbs) (premise0 : FODerivable R (jNLt fid idv)) (premise1 : FODerivable R (jManyMiss rest (cSym fid cKFvar fbs))) : FODerivable R (jManyMiss (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs)) := by
  apply FODerivable.intro member [idv, bs, k, w, rest, fid, fbs] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rManyMissGt idv bs k w rest fid fbs).2
  · rw [(inst_rManyMissGt idv bs k w rest fid fbs).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl <;> assumption

theorem inst_rManyNofv (entries o t : Pattern) :
    rManyNofv.instPremises [entries, o, t] = [jHasFv t cFalse] ∧
      rManyNofv.instConclusion [entries, o, t] = (jMany entries o t t) := by
  simp [rManyNofv, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cFalse, jHasFv, jMany]

theorem sound_rManyNofv {P : Pattern → Prop}
    (sound : ∀ entries o t : Pattern, P (jHasFv t cFalse) → P (jMany entries o t t)) :
    ∀ args : List Pattern, args.length = rManyNofv.vars.length →
      (∀ premise ∈ rManyNofv.instPremises args, P premise) → P (rManyNofv.instConclusion args) := by
  intro args length premises
  match args, length with
  | [entries, o, t], _ =>
      rw [(inst_rManyNofv entries o t).1] at premises
      rw [(inst_rManyNofv entries o t).2]
      exact sound entries o t (premises _ (by simp))

theorem intro_rManyNofv {R : List FORule} (member : rManyNofv ∈ R) {entries o t : Pattern}
    (data_entries : IsData entries) (data_o : IsData o) (data_t : IsData t) (premise0 : FODerivable R (jHasFv t cFalse)) : FODerivable R (jMany entries o t t) := by
  apply FODerivable.intro member [entries, o, t] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl <;> assumption
  · exact (inst_rManyNofv entries o t).2
  · rw [(inst_rManyNofv entries o t).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl
    assumption

theorem inst_rManyConst (entries o idv bs ts d us e g : Pattern) :
    rManyConst.instPremises [entries, o, idv, bs, ts, d, us, e, g] = [jManyArgs entries o bs ts us, jAnnArgs bs us e g] ∧
      rManyConst.instConclusion [entries, o, idv, bs, ts, d, us, e, g] = (jMany entries o (cApp (cSym idv cKConst bs) ts (cAnn d cTrue)) (cApp (cSym idv cKConst bs) us (cAnn e g))) := by
  simp [rManyConst, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cAnn, cApp, cKConst, cSym, cTrue, jAnnArgs, jMany, jManyArgs]

theorem sound_rManyConst {P : Pattern → Prop}
    (sound : ∀ entries o idv bs ts d us e g : Pattern, P (jManyArgs entries o bs ts us) → P (jAnnArgs bs us e g) → P (jMany entries o (cApp (cSym idv cKConst bs) ts (cAnn d cTrue)) (cApp (cSym idv cKConst bs) us (cAnn e g)))) :
    ∀ args : List Pattern, args.length = rManyConst.vars.length →
      (∀ premise ∈ rManyConst.instPremises args, P premise) → P (rManyConst.instConclusion args) := by
  intro args length premises
  match args, length with
  | [entries, o, idv, bs, ts, d, us, e, g], _ =>
      rw [(inst_rManyConst entries o idv bs ts d us e g).1] at premises
      rw [(inst_rManyConst entries o idv bs ts d us e g).2]
      exact sound entries o idv bs ts d us e g (premises _ (by simp)) (premises _ (by simp))

theorem intro_rManyConst {R : List FORule} (member : rManyConst ∈ R) {entries o idv bs ts d us e g : Pattern}
    (data_entries : IsData entries) (data_o : IsData o) (data_idv : IsData idv) (data_bs : IsData bs) (data_ts : IsData ts) (data_d : IsData d) (data_us : IsData us) (data_e : IsData e) (data_g : IsData g) (premise0 : FODerivable R (jManyArgs entries o bs ts us)) (premise1 : FODerivable R (jAnnArgs bs us e g)) : FODerivable R (jMany entries o (cApp (cSym idv cKConst bs) ts (cAnn d cTrue)) (cApp (cSym idv cKConst bs) us (cAnn e g))) := by
  apply FODerivable.intro member [entries, o, idv, bs, ts, d, us, e, g] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rManyConst entries o idv bs ts d us e g).2
  · rw [(inst_rManyConst entries o idv bs ts d us e g).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl <;> assumption

theorem inst_rManyAbsent (entries o fid fbs ts d us e g : Pattern) :
    rManyAbsent.instPremises [entries, o, fid, fbs, ts, d, us, e, g] = [jManyMiss entries (cSym fid cKFvar fbs), jManyArgs entries o fbs ts us, jAnnArgs fbs us e g] ∧
      rManyAbsent.instConclusion [entries, o, fid, fbs, ts, d, us, e, g] = (jMany entries o (cApp (cSym fid cKFvar fbs) ts (cAnn d cTrue)) (cApp (cSym fid cKFvar fbs) us (cAnn e cTrue))) := by
  simp [rManyAbsent, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cAnn, cApp, cKFvar, cSym, cTrue, fvarSym, jAnnArgs, jMany, jManyArgs, jManyMiss]

theorem sound_rManyAbsent {P : Pattern → Prop}
    (sound : ∀ entries o fid fbs ts d us e g : Pattern, P (jManyMiss entries (cSym fid cKFvar fbs)) → P (jManyArgs entries o fbs ts us) → P (jAnnArgs fbs us e g) → P (jMany entries o (cApp (cSym fid cKFvar fbs) ts (cAnn d cTrue)) (cApp (cSym fid cKFvar fbs) us (cAnn e cTrue)))) :
    ∀ args : List Pattern, args.length = rManyAbsent.vars.length →
      (∀ premise ∈ rManyAbsent.instPremises args, P premise) → P (rManyAbsent.instConclusion args) := by
  intro args length premises
  match args, length with
  | [entries, o, fid, fbs, ts, d, us, e, g], _ =>
      rw [(inst_rManyAbsent entries o fid fbs ts d us e g).1] at premises
      rw [(inst_rManyAbsent entries o fid fbs ts d us e g).2]
      exact sound entries o fid fbs ts d us e g (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp))

theorem intro_rManyAbsent {R : List FORule} (member : rManyAbsent ∈ R) {entries o fid fbs ts d us e g : Pattern}
    (data_entries : IsData entries) (data_o : IsData o) (data_fid : IsData fid) (data_fbs : IsData fbs) (data_ts : IsData ts) (data_d : IsData d) (data_us : IsData us) (data_e : IsData e) (data_g : IsData g) (premise0 : FODerivable R (jManyMiss entries (cSym fid cKFvar fbs))) (premise1 : FODerivable R (jManyArgs entries o fbs ts us)) (premise2 : FODerivable R (jAnnArgs fbs us e g)) : FODerivable R (jMany entries o (cApp (cSym fid cKFvar fbs) ts (cAnn d cTrue)) (cApp (cSym fid cKFvar fbs) us (cAnn e cTrue))) := by
  apply FODerivable.intro member [entries, o, fid, fbs, ts, d, us, e, g] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rManyAbsent entries o fid fbs ts d us e g).2
  · rw [(inst_rManyAbsent entries o fid fbs ts d us e g).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl <;> assumption

theorem inst_rManySelected (entries o fid fbs n v ts d us w r : Pattern) :
    rManySelected.instPremises [entries, o, fid, fbs, n, v, ts, d, us, w, r] = [jManyHit entries (cSym fid cKFvar fbs) n v, jManyArgs entries o fbs ts us, jShift o n v w, jSubstTop n us w r] ∧
      rManySelected.instConclusion [entries, o, fid, fbs, n, v, ts, d, us, w, r] = (jMany entries o (cApp (cSym fid cKFvar fbs) ts (cAnn d cTrue)) r) := by
  simp [rManySelected, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cAnn, cApp, cKFvar, cSym, cTrue, fvarSym, jMany, jManyArgs, jManyHit, jShift, jSubstTop]

theorem sound_rManySelected {P : Pattern → Prop}
    (sound : ∀ entries o fid fbs n v ts d us w r : Pattern, P (jManyHit entries (cSym fid cKFvar fbs) n v) → P (jManyArgs entries o fbs ts us) → P (jShift o n v w) → P (jSubstTop n us w r) → P (jMany entries o (cApp (cSym fid cKFvar fbs) ts (cAnn d cTrue)) r)) :
    ∀ args : List Pattern, args.length = rManySelected.vars.length →
      (∀ premise ∈ rManySelected.instPremises args, P premise) → P (rManySelected.instConclusion args) := by
  intro args length premises
  match args, length with
  | [entries, o, fid, fbs, n, v, ts, d, us, w, r], _ =>
      rw [(inst_rManySelected entries o fid fbs n v ts d us w r).1] at premises
      rw [(inst_rManySelected entries o fid fbs n v ts d us w r).2]
      exact sound entries o fid fbs n v ts d us w r (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp))

theorem intro_rManySelected {R : List FORule} (member : rManySelected ∈ R) {entries o fid fbs n v ts d us w r : Pattern}
    (data_entries : IsData entries) (data_o : IsData o) (data_fid : IsData fid) (data_fbs : IsData fbs) (data_n : IsData n) (data_v : IsData v) (data_ts : IsData ts) (data_d : IsData d) (data_us : IsData us) (data_w : IsData w) (data_r : IsData r) (premise0 : FODerivable R (jManyHit entries (cSym fid cKFvar fbs) n v)) (premise1 : FODerivable R (jManyArgs entries o fbs ts us)) (premise2 : FODerivable R (jShift o n v w)) (premise3 : FODerivable R (jSubstTop n us w r)) : FODerivable R (jMany entries o (cApp (cSym fid cKFvar fbs) ts (cAnn d cTrue)) r) := by
  apply FODerivable.intro member [entries, o, fid, fbs, n, v, ts, d, us, w, r] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rManySelected entries o fid fbs n v ts d us w r).2
  · rw [(inst_rManySelected entries o fid fbs n v ts d us w r).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl <;> assumption

theorem inst_rManyArgsNil (entries o : Pattern) :
    rManyArgsNil.instPremises [entries, o] = [] ∧
      rManyArgsNil.instConclusion [entries, o] = (jManyArgs entries o cNil cNil cNil) := by
  simp [rManyArgsNil, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cNil, jManyArgs]

theorem sound_rManyArgsNil {P : Pattern → Prop}
    (sound : ∀ entries o : Pattern, P (jManyArgs entries o cNil cNil cNil)) :
    ∀ args : List Pattern, args.length = rManyArgsNil.vars.length →
      (∀ premise ∈ rManyArgsNil.instPremises args, P premise) → P (rManyArgsNil.instConclusion args) := by
  intro args length premises
  match args, length with
  | [entries, o], _ =>
      rw [(inst_rManyArgsNil entries o).1] at premises
      rw [(inst_rManyArgsNil entries o).2]
      exact sound entries o 

theorem intro_rManyArgsNil {R : List FORule} (member : rManyArgsNil ∈ R) {entries o : Pattern}
    (data_entries : IsData entries) (data_o : IsData o)  : FODerivable R (jManyArgs entries o cNil cNil cNil) := by
  apply FODerivable.intro member [entries, o] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl <;> assumption
  · exact (inst_rManyArgsNil entries o).2
  · rw [(inst_rManyArgsNil entries o).1]
    intro goal included
    simp only [List.not_mem_nil] at included

theorem inst_rManyArgsCons (entries o b bs t ts u us k : Pattern) :
    rManyArgsCons.instPremises [entries, o, b, bs, t, ts, u, us, k] = [jNAdd o b k, jNWord k, jMany entries k t u, jManyArgs entries o bs ts us] ∧
      rManyArgsCons.instConclusion [entries, o, b, bs, t, ts, u, us, k] = (jManyArgs entries o (cCons b bs) (cCons t ts) (cCons u us)) := by
  simp [rManyArgsCons, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cCons, jMany, jManyArgs, jNAdd, jNWord]

theorem sound_rManyArgsCons {P : Pattern → Prop}
    (sound : ∀ entries o b bs t ts u us k : Pattern, P (jNAdd o b k) → P (jNWord k) → P (jMany entries k t u) → P (jManyArgs entries o bs ts us) → P (jManyArgs entries o (cCons b bs) (cCons t ts) (cCons u us))) :
    ∀ args : List Pattern, args.length = rManyArgsCons.vars.length →
      (∀ premise ∈ rManyArgsCons.instPremises args, P premise) → P (rManyArgsCons.instConclusion args) := by
  intro args length premises
  match args, length with
  | [entries, o, b, bs, t, ts, u, us, k], _ =>
      rw [(inst_rManyArgsCons entries o b bs t ts u us k).1] at premises
      rw [(inst_rManyArgsCons entries o b bs t ts u us k).2]
      exact sound entries o b bs t ts u us k (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp))

theorem intro_rManyArgsCons {R : List FORule} (member : rManyArgsCons ∈ R) {entries o b bs t ts u us k : Pattern}
    (data_entries : IsData entries) (data_o : IsData o) (data_b : IsData b) (data_bs : IsData bs) (data_t : IsData t) (data_ts : IsData ts) (data_u : IsData u) (data_us : IsData us) (data_k : IsData k) (premise0 : FODerivable R (jNAdd o b k)) (premise1 : FODerivable R (jNWord k)) (premise2 : FODerivable R (jMany entries k t u)) (premise3 : FODerivable R (jManyArgs entries o bs ts us)) : FODerivable R (jManyArgs entries o (cCons b bs) (cCons t ts) (cCons u us)) := by
  apply FODerivable.intro member [entries, o, b, bs, t, ts, u, us, k] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rManyArgsCons entries o b bs t ts u us k).2
  · rw [(inst_rManyArgsCons entries o b bs t ts u us k).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl <;> assumption

theorem inst_rInstantiateManyNil (phi : Pattern) :
    rInstantiateManyNil.instPremises [phi] = [jThm phi, jDepth phi cN0] ∧
      rInstantiateManyNil.instConclusion [phi] = (jThm phi) := by
  simp [rInstantiateManyNil, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, cN0, jDepth, jThm]

theorem sound_rInstantiateManyNil {P : Pattern → Prop}
    (sound : ∀ phi : Pattern, P (jThm phi) → P (jDepth phi cN0) → P (jThm phi)) :
    ∀ args : List Pattern, args.length = rInstantiateManyNil.vars.length →
      (∀ premise ∈ rInstantiateManyNil.instPremises args, P premise) → P (rInstantiateManyNil.instConclusion args) := by
  intro args length premises
  match args, length with
  | [phi], _ =>
      rw [(inst_rInstantiateManyNil phi).1] at premises
      rw [(inst_rInstantiateManyNil phi).2]
      exact sound phi (premises _ (by simp)) (premises _ (by simp))

theorem intro_rInstantiateManyNil {R : List FORule} (member : rInstantiateManyNil ∈ R) {phi : Pattern}
    (data_phi : IsData phi) (premise0 : FODerivable R (jThm phi)) (premise1 : FODerivable R (jDepth phi cN0)) : FODerivable R (jThm phi) := by
  apply FODerivable.intro member [phi] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl
    assumption
  · exact (inst_rInstantiateManyNil phi).2
  · rw [(inst_rInstantiateManyNil phi).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl <;> assumption

theorem inst_rInstantiateManyCons (rep reps entry entries phi psi : Pattern) :
    rInstantiateManyCons.instPremises [rep, reps, entry, entries, phi, psi] = [jThm phi, jManyPrepare (cCons rep reps) (cCons entry entries), jMany (cCons entry entries) cN0 phi psi, jDepth psi cN0] ∧
      rInstantiateManyCons.instConclusion [rep, reps, entry, entries, phi, psi] = (jThm psi) := by
  simp [rInstantiateManyCons, FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, ab_apply, mv, ab_fvar_hit, ab_fvar_miss, cCons, cN0, jDepth, jMany, jManyPrepare, jThm]

theorem sound_rInstantiateManyCons {P : Pattern → Prop}
    (sound : ∀ rep reps entry entries phi psi : Pattern, P (jThm phi) → P (jManyPrepare (cCons rep reps) (cCons entry entries)) → P (jMany (cCons entry entries) cN0 phi psi) → P (jDepth psi cN0) → P (jThm psi)) :
    ∀ args : List Pattern, args.length = rInstantiateManyCons.vars.length →
      (∀ premise ∈ rInstantiateManyCons.instPremises args, P premise) → P (rInstantiateManyCons.instConclusion args) := by
  intro args length premises
  match args, length with
  | [rep, reps, entry, entries, phi, psi], _ =>
      rw [(inst_rInstantiateManyCons rep reps entry entries phi psi).1] at premises
      rw [(inst_rInstantiateManyCons rep reps entry entries phi psi).2]
      exact sound rep reps entry entries phi psi (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp)) (premises _ (by simp))

theorem intro_rInstantiateManyCons {R : List FORule} (member : rInstantiateManyCons ∈ R) {rep reps entry entries phi psi : Pattern}
    (data_rep : IsData rep) (data_reps : IsData reps) (data_entry : IsData entry) (data_entries : IsData entries) (data_phi : IsData phi) (data_psi : IsData psi) (premise0 : FODerivable R (jThm phi)) (premise1 : FODerivable R (jManyPrepare (cCons rep reps) (cCons entry entries))) (premise2 : FODerivable R (jMany (cCons entry entries) cN0 phi psi)) (premise3 : FODerivable R (jDepth psi cN0)) : FODerivable R (jThm psi) := by
  apply FODerivable.intro member [rep, reps, entry, entries, phi, psi] rfl
  · intro argument included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact (inst_rInstantiateManyCons rep reps entry entries phi psi).2
  · rw [(inst_rInstantiateManyCons rep reps entry entries phi psi).1]
    intro goal included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl <;> assumption

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
