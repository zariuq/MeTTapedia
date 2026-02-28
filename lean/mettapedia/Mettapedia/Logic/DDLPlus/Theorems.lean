import Mettapedia.Logic.DDLPlus.Core

/-!
# Carmo-Jones DDL+ Theorems

All CJ theorems from `GewirthPGCProof/CJDDLplus.thy:128–178`, proven semantically
by unfolding the shallow embedding. These are the axiomatic characterisation
results from Carmo & Jones (2002), pp. 293ff.

## Contents

- §1 Auxiliary lemmas (C_2–C_8)
- §2 CJ axiomatic characterisation (CJ_3–CJ_15)
- §3 Bridge relations (conditional ↔ actual/ideal obligation)
-/

namespace Mettapedia.Logic.DDLPlus.Theorems

open Mettapedia.Logic.DDLPlus.Core

variable {c w : Type*} (F : DDLPlusFrame w)

/-! ## §1 Auxiliary Lemmas

Semantic lemmas extracted from Benzmüller et al. (CJDDLplus.thy:128–134). -/

/-- C_2: conditional obligation implies S5-possibility of conjunction.
    CJDDLplus.thy:128 -/
theorem C_2 (A B : Meaning c w) :
    modal_valid (pimp (cond_obl F A B) (dia_S5 (pand B A))) :=
  fun _ _ hob => F.sem_5ab hob

/-- C_3: conjunction of obligations under instantiation.
    CJDDLplus.thy:129 -/
theorem C_3 (A B C' : Meaning c w) :
    modal_valid (pimp (pand (pand (dia_S5 (pand A (pand B C'))) (cond_obl F B A))
      (cond_obl F C' A)) (cond_obl F (pand B C') A)) :=
  fun _ _ ⟨⟨hdia, hob1⟩, hob2⟩ => F.sem_5c _ _ _ hdia hob1 hob2

/-- C_4: restriction of obligation to subcontexts.
    CJDDLplus.thy:130 -/
theorem C_4 (A B C' : Meaning c w) :
    modal_valid (pimp (pand (pand (box_S5 (pimp A B)) (dia_S5 (pand A C')))
      (cond_obl F C' B)) (cond_obl F C' A)) :=
  fun _ _ ⟨⟨hall, hdia⟩, hob⟩ =>
    F.sem_5e _ _ _ (fun v ha => hall v ha) hob hdia

/-- C_5: obligation respects S5-equivalence of contexts.
    CJDDLplus.thy:131 -/
theorem C_5 (A B C' : Meaning c w) :
    modal_valid (pimp (box_S5 (pequ A B)) (pimp (cond_obl F C' A) (cond_obl F C' B))) := by
  intro ctx v heq hob
  have ⟨v', hav, hcv⟩ := F.sem_5ab hob
  exact F.sem_5e _ _ _ (fun v hb => (heq v).mpr hb) hob ⟨v', (heq v').mp hav, hcv⟩

/-- C_6: obligation respects conditional equivalence.
    CJDDLplus.thy:132 -/
theorem C_6 (A B C' : Meaning c w) :
    modal_valid (pimp (box_S5 (pimp C' (pequ A B)))
      (pequ (cond_obl F A C') (cond_obl F B C'))) := by
  intro ctx v hcond
  constructor
  · intro hob
    exact (F.sem_5b _ _ _ (fun v => ⟨
      fun ⟨hc, ha⟩ => ⟨hc, (hcond v hc).mp ha⟩,
      fun ⟨hc, hb⟩ => ⟨hc, (hcond v hc).mpr hb⟩⟩)).mp hob
  · intro hob
    exact (F.sem_5b _ _ _ (fun v => ⟨
      fun ⟨hc, hb⟩ => ⟨hc, (hcond v hc).mpr hb⟩,
      fun ⟨hc, ha⟩ => ⟨hc, (hcond v hc).mp ha⟩⟩)).mp hob

/-- C_7: conditional obligation is S5-necessary (world-independent).
    CJDDLplus.thy:133 -/
theorem C_7 (A B : Meaning c w) :
    modal_valid (pimp (cond_obl F A B) (box_S5 (cond_obl F A B))) :=
  fun _ _ hob _ => hob

/-- C_8: conditional obligation implies material conditional under ⊤.
    CJDDLplus.thy:134 -/
theorem C_8 (A B : Meaning c w) :
    modal_valid (pimp (cond_obl F A B) (cond_obl F (pimp B A) ptop)) := by
  intro ctx v hob
  have hsub : ∀ v, B ctx v → True := fun _ _ => trivial
  have h := F.sem_5bd4 hob hsub
  -- h : ob ⊤ (¬B ∨ (B ∧ A)), need: ob ⊤ (B → A)
  exact (F.sem_5b _ _ _ (fun v => ⟨
    fun ⟨_, hor⟩ => ⟨trivial, fun hb => hor.elim (absurd hb) And.right⟩,
    fun ⟨_, himp⟩ => ⟨trivial, by
      by_cases hb : B ctx v
      · exact Or.inr ⟨hb, himp hb⟩
      · exact Or.inl hb⟩⟩)).mp h

/-! ## §2 CJ Axiomatic Characterisation

Theorems CJ_3–CJ_15 from Carmo & Jones (2002), pp. 293ff.
CJDDLplus.thy:140–178. -/

/-- CJ_3: □ₚ implies □ₐ (possible necessity → actual necessity).
    CJDDLplus.thy:140 -/
theorem CJ_3 (A : Meaning c w) :
    modal_valid (pimp (box_p F A) (box_a F A)) :=
  fun _ v hbox v' hav => hbox v' (F.sem_4a v v' hav)

/-- CJ_4: contradictions cannot be conditionally obligatory.
    CJDDLplus.thy:141 -/
theorem CJ_4 (A : Meaning c w) :
    modal_valid (pnot (cond_obl F pbot A)) :=
  fun _ _ hob => F.sem_5a _ hob

/-- CJ_5⁻: weakened conjunction of obligations (requires instantiation witness).
    CJDDLplus.thy:144 -/
theorem CJ_5_minus (A B C' : Meaning c w) :
    modal_valid (pimp (pand (dia_S5 (pand A (pand B C')))
      (pand (cond_obl F B A) (cond_obl F C' A)))
      (cond_obl F (pand B C') A)) :=
  fun _ _ ⟨hdia, hob1, hob2⟩ => F.sem_5c _ _ _ hdia hob1 hob2

/-- CJ_6: obligation persists under conjunction with the obligated content.
    CJDDLplus.thy:146 -/
theorem CJ_6 (A B : Meaning c w) :
    modal_valid (pimp (cond_obl F A B) (cond_obl F A (pand B A))) := by
  intro ctx v hob
  have hsub : ∀ v, B ctx v ∧ A ctx v → B ctx v := fun _ h => h.1
  have ⟨v', hbv, hav⟩ := F.sem_5ab hob
  exact F.sem_5e _ _ _ hsub hob ⟨v', ⟨hbv, hav⟩, hav⟩

/-- CJ_7: conditional obligation under modal equivalence.
    CJDDLplus.thy:147. Valid only under classical (not LD) validity. -/
theorem CJ_7 (A B C' : Meaning c w) :
    modal_valid (pequ A B) → modal_valid (pequ (cond_obl F C' A) (cond_obl F C' B)) := by
  intro heq ctx v
  constructor
  · intro hob
    have ⟨v', hav, hcv⟩ := F.sem_5ab hob
    exact F.sem_5e _ _ _ (fun v hb => (heq ctx v).mpr hb) hob ⟨v', (heq ctx v').mp hav, hcv⟩
  · intro hob
    have ⟨v', hbv, hcv⟩ := F.sem_5ab hob
    exact F.sem_5e _ _ _ (fun v ha => (heq ctx v).mp ha) hob ⟨v', (heq ctx v').mpr hbv, hcv⟩

/-- CJ_8: conditional obligation under conditional equivalence.
    CJDDLplus.thy:148. Valid only under classical (not LD) validity. -/
theorem CJ_8 (A B C' : Meaning c w) :
    modal_valid (pimp C' (pequ A B)) →
    modal_valid (pequ (cond_obl F A C') (cond_obl F B C')) :=
  fun hcond ctx v => C_6 F A B C' ctx v (fun v hc => hcond ctx v hc)

/-- CJ_9a: conditional obligation is S5 w.r.t. □ₚ (◇ₚ → □ₚ).
    CJDDLplus.thy:150 -/
theorem CJ_9a (A B : Meaning c w) :
    modal_valid (pimp (dia_p F (cond_obl F A B)) (box_p F (cond_obl F A B))) :=
  fun _ _ ⟨_, _, hob⟩ _ _ => hob

/-- CJ_9p: conditional obligation is S5 w.r.t. □ₐ (◇ₐ → □ₐ).
    CJDDLplus.thy:151 -/
theorem CJ_9p (A B : Meaning c w) :
    modal_valid (pimp (dia_a F (cond_obl F A B)) (box_a F (cond_obl F A B))) :=
  fun _ _ ⟨_, _, hob⟩ _ _ => hob

/-- CJ_9_var_a: conditional obligation implies □ₐ-necessity.
    CJDDLplus.thy:152 -/
theorem CJ_9_var_a (A B : Meaning c w) :
    modal_valid (pimp (cond_obl F A B) (box_a F (cond_obl F A B))) :=
  fun _ _ hob _ _ => hob

/-- CJ_9_var_b: conditional obligation implies □ₚ-necessity.
    CJDDLplus.thy:153 -/
theorem CJ_9_var_b (A B : Meaning c w) :
    modal_valid (pimp (cond_obl F A B) (box_p F (cond_obl F A B))) :=
  fun _ _ hob _ _ => hob

/-- CJ_10: restriction of obligation under possibility witness.
    CJDDLplus.thy:154 -/
theorem CJ_10 (A B C' : Meaning c w) :
    modal_valid (pimp (pand (dia_p F (pand A (pand B C'))) (cond_obl F C' B))
      (cond_obl F C' (pand A B))) := by
  intro ctx v ⟨⟨v', hpv, ha, hb, hc⟩, hob⟩
  exact F.sem_5e _ _ _ (fun _ h => h.2) hob ⟨v', ⟨ha, hb⟩, hc⟩

/-- CJ_11a_var: actual obligation conjunction (with instantiation witness).
    CJDDLplus.thy:157 -/
theorem CJ_11a_var (A B : Meaning c w) :
    modal_valid (pimp (pand (dia_a F (pand A B)) (pand (actual_obl F A) (actual_obl F B)))
      (actual_obl F (pand A B))) := by
  intro ctx v ⟨⟨v', hav', ha, hb⟩, ⟨hoba, v₁, hav₁, hna⟩, hobb, v₂, hav₂, hnb⟩
  exact ⟨F.sem_5c _ _ _ ⟨v', hav', ha, hb⟩ hoba hobb,
         v₁, hav₁, fun ⟨ha', _⟩ => hna ha'⟩

/-- CJ_11p_var: ideal obligation conjunction (with instantiation witness).
    CJDDLplus.thy:160 -/
theorem CJ_11p_var (A B : Meaning c w) :
    modal_valid (pimp (pand (dia_p F (pand A B)) (pand (ideal_obl F A) (ideal_obl F B)))
      (ideal_obl F (pand A B))) := by
  intro ctx v ⟨⟨v', hpv', ha, hb⟩, ⟨hoba, v₁, hpv₁, hna⟩, hobb, v₂, hpv₂, hnb⟩
  exact ⟨F.sem_5c _ _ _ ⟨v', hpv', ha, hb⟩ hoba hobb,
         v₁, hpv₁, fun ⟨ha', _⟩ => hna ha'⟩

/-- CJ_12a: Kant's law for actual obligation (necessary → not obligatory).
    CJDDLplus.thy:162 -/
theorem CJ_12a (A : Meaning c w) :
    modal_valid (pimp (box_a F A)
      (pand (pnot (actual_obl F A)) (pnot (actual_obl F (pnot A))))) := by
  intro ctx v hbox
  exact ⟨fun ⟨_, v', hav, hna⟩ => hna (hbox v' hav),
         fun ⟨hob, _⟩ => (F.sem_5ab hob).elim fun v' ⟨hav, hn⟩ => hn (hbox v' hav)⟩

/-- CJ_12p: Kant's law for ideal obligation (necessary → not obligatory).
    CJDDLplus.thy:163 -/
theorem CJ_12p (A : Meaning c w) :
    modal_valid (pimp (box_p F A)
      (pand (pnot (ideal_obl F A)) (pnot (ideal_obl F (pnot A))))) := by
  intro ctx v hbox
  exact ⟨fun ⟨_, v', hpv, hna⟩ => hna (hbox v' hpv),
         fun ⟨hob, _⟩ => (F.sem_5ab hob).elim fun v' ⟨hpv, hn⟩ => hn (hbox v' hpv)⟩

/-- CJ_13a: actual obligation respects □ₐ-equivalence.
    CJDDLplus.thy:165 -/
theorem CJ_13a (A B : Meaning c w) :
    modal_valid (pimp (box_a F (pequ A B)) (pequ (actual_obl F A) (actual_obl F B))) := by
  intro ctx v hbox
  have hiff : ∀ v', F.av v v' → (A ctx v' ↔ B ctx v') := hbox
  constructor
  · intro ⟨hob, v', hav, hna⟩
    exact ⟨(F.sem_5b _ _ _ (fun v' => ⟨
      fun ⟨h1, h2⟩ => ⟨h1, (hiff v' h1).mp h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, (hiff v' h1).mpr h2⟩⟩)).mp hob,
      v', hav, fun hb => hna ((hiff v' hav).mpr hb)⟩
  · intro ⟨hob, v', hav, hnb⟩
    exact ⟨(F.sem_5b _ _ _ (fun v' => ⟨
      fun ⟨h1, h2⟩ => ⟨h1, (hiff v' h1).mpr h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, (hiff v' h1).mp h2⟩⟩)).mp hob,
      v', hav, fun ha => hnb ((hiff v' hav).mp ha)⟩

/-- CJ_13p: ideal obligation respects □ₚ-equivalence.
    CJDDLplus.thy:166 -/
theorem CJ_13p (A B : Meaning c w) :
    modal_valid (pimp (box_p F (pequ A B)) (pequ (ideal_obl F A) (ideal_obl F B))) := by
  intro ctx v hbox
  have hiff : ∀ v', F.pv v v' → (A ctx v' ↔ B ctx v') := hbox
  constructor
  · intro ⟨hob, v', hpv, hna⟩
    exact ⟨(F.sem_5b _ _ _ (fun v' => ⟨
      fun ⟨h1, h2⟩ => ⟨h1, (hiff v' h1).mp h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, (hiff v' h1).mpr h2⟩⟩)).mp hob,
      v', hpv, fun hb => hna ((hiff v' hpv).mpr hb)⟩
  · intro ⟨hob, v', hpv, hnb⟩
    exact ⟨(F.sem_5b _ _ _ (fun v' => ⟨
      fun ⟨h1, h2⟩ => ⟨h1, (hiff v' h1).mpr h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, (hiff v' h1).mp h2⟩⟩)).mp hob,
      v', hpv, fun ha => hnb ((hiff v' hpv).mp ha)⟩

/-- CJ_O_O: conditional obligation implies material conditional under ⊤.
    CJDDLplus.thy:168 -/
theorem CJ_O_O (A B : Meaning c w) :
    modal_valid (pimp (cond_obl F A B) (cond_obl F (pimp B A) ptop)) :=
  C_8 F A B

/-! ## §3 Bridge Relations

Connections between conditional, actual, and ideal obligations.
CJDDLplus.thy:171–178. -/

/-- CJ_Oi_Oa: ideal obligation + actual possibility ↔ actual obligation.
    CJDDLplus.thy:171 -/
theorem CJ_Oi_Oa (A : Meaning c w) :
    modal_valid (pimp (pand (pand (ideal_obl F A) (dia_a F A)) (dia_a F (pnot A)))
      (actual_obl F A)) := by
  intro ctx v ⟨⟨⟨hob, _⟩, v₁, hav₁, ha₁⟩, v₂, hav₂, hna₂⟩
  exact ⟨F.sem_5e _ _ _ (F.sem_4a v) hob ⟨v₁, hav₁, ha₁⟩, v₂, hav₂, hna₂⟩

/-- CJ_14a: conditional obligation + □ₐ-context + violation → actual obligation.
    CJDDLplus.thy:174 -/
theorem CJ_14a (A B : Meaning c w) :
    modal_valid (pimp (pand (pand (pand (cond_obl F A B) (box_a F B)) (dia_a F A))
      (dia_a F (pnot A))) (actual_obl F A)) := by
  intro ctx v ⟨⟨⟨hob, hbox⟩, v₁, hav₁, ha₁⟩, v₂, hav₂, hna₂⟩
  exact ⟨F.sem_5e _ _ _ hbox hob ⟨v₁, hav₁, ha₁⟩, v₂, hav₂, hna₂⟩

/-- CJ_14p: conditional obligation + □ₚ-context + violation → ideal obligation.
    CJDDLplus.thy:175 -/
theorem CJ_14p (A B : Meaning c w) :
    modal_valid (pimp (pand (pand (pand (cond_obl F A B) (box_p F B)) (dia_p F A))
      (dia_p F (pnot A))) (ideal_obl F A)) := by
  intro ctx v ⟨⟨⟨hob, hbox⟩, v₁, hpv₁, ha₁⟩, v₂, hpv₂, hna₂⟩
  exact ⟨F.sem_5e _ _ _ hbox hob ⟨v₁, hpv₁, ha₁⟩, v₂, hpv₂, hna₂⟩

/-- CJ_15a: conditional obligation + satisfiability + violability → actual material obligation.
    CJDDLplus.thy:177 -/
theorem CJ_15a (A B : Meaning c w) :
    modal_valid (pimp (pand (pand (cond_obl F A B) (dia_a F (pand B A)))
      (dia_a F (pand B (pnot A)))) (actual_obl F (pimp B A))) := by
  intro ctx v ⟨⟨hob, v₁, hav₁, hb₁, ha₁⟩, v₂, hav₂, hb₂, hna₂⟩
  have h_top := CJ_O_O F A B ctx v hob
  exact ⟨F.sem_5e _ _ _ (fun _ _ => trivial) h_top ⟨v₁, hav₁, fun _ => ha₁⟩,
         v₂, hav₂, fun himp => hna₂ (himp hb₂)⟩

/-- CJ_15p: conditional obligation + satisfiability + violability → ideal material obligation.
    CJDDLplus.thy:178 -/
theorem CJ_15p (A B : Meaning c w) :
    modal_valid (pimp (pand (pand (cond_obl F A B) (dia_p F (pand B A)))
      (dia_p F (pand B (pnot A)))) (ideal_obl F (pimp B A))) := by
  intro ctx v ⟨⟨hob, v₁, hpv₁, hb₁, ha₁⟩, v₂, hpv₂, hb₂, hna₂⟩
  have h_top := CJ_O_O F A B ctx v hob
  exact ⟨F.sem_5e _ _ _ (fun _ _ => trivial) h_top ⟨v₁, hpv₁, fun _ => ha₁⟩,
         v₂, hpv₂, fun himp => hna₂ (himp hb₂)⟩

/-! ## §4 Obligation Redefinition

The characterisation result: ob is equivalent to its recursive unfolding
via sem_5e and sem_5ab. CJDDLplus.thy:75. -/

/-- Obligation is equivalent to instantiation + universal restriction.
    CJDDLplus.thy:75 -/
theorem ob_characterisation {X Y : WProp w} :
    F.ob X Y ↔ ((∃ v, X v ∧ Y v) ∧ ∀ Z : WProp w, (∀ v, Z v → X v) → (∃ v, Z v ∧ Y v) → F.ob Z Y) := by
  constructor
  · intro h; exact ⟨F.sem_5ab h, fun Z hsub hinst => F.sem_5e _ _ _ hsub h hinst⟩
  · intro ⟨hinst, huniv⟩; exact huniv X (fun _ hx => hx) hinst

end Mettapedia.Logic.DDLPlus.Theorems
