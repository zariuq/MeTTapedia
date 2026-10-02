import Mettapedia.Logic.Diagonal.Lawvere
import Mettapedia.Logic.Diagonal.Kleene
import Mettapedia.Logic.Diagonal.Combinatory
import Mettapedia.CategoryTheory.LawvereFixedPoint
import Mettapedia.GSLT.Logic.ReflectiveBubble
import Mettapedia.GSLT.Logic.KripkeFixedPoint
import Mettapedia.GSLT.GraphTheory.ReflectiveBetaBubble
import Mettapedia.GSLT.GraphTheory.OracleStratification
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DropFreeTermination
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuoteMeetingPoint
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannelInternalDecision
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ProofByReflection

/-!
# Reflection and the diagonal: one structure behind rho and carved fragments

Codes that run on codes, point-surjectively up to a relation, force fixed
points (positive reading) and forbid total internal decisions (negative
reading).  The escapes are partiality and stratification.

* `Logic.Diagonal.Lawvere`: the diagonal step relative to a relation and a
  class of maps; Lawvere's theorem for types, Cantor, Tarski's form, the
  abstract Rice theorem, and code/behaviour retractions.
* `CategoryTheory.LawvereFixedPoint`: weak point-surjectivity and Lawvere's
  theorem with finite products and with exponentials, with controls in the
  category of types.
* `Logic.Diagonal.Kleene`: Kleene's recursion theorem and Rice's theorem from
  the diagonal, for partial recursive codes up to extensional equality.
* `Logic.Diagonal.Combinatory`: reflexive structures (point-surjective onto
  polynomial maps up to an equivalence): fixed points, the Scott–Curry form of
  the negative reading, undetermined diagonals of sound deciders, and proper
  internal carve-outs.
* `GSLT.Logic.ReflectiveBubble`, `GSLT.GraphTheory.ReflectiveBetaBubble`: the
  default β-bubble is reflective; no λ-term decides β-conversion, and every
  internally realised fragment decision leaves its diagonal `outsideFragment`;
  a classical total decision exists one stage up.
* `GSLT.Logic.KripkeFixedPoint`: the partial escape, as the least fixed point
  in the knowledge order, consistent by duality, with the diagonal undetermined
  and verdicts as outcomes.
* `GSLT.GraphTheory.OracleStratification`: the stratified escape through the
  oracle-stage criterion; an admissible oracle decides without distinguishing,
  an inadmissible one distinguishes.
* `RhoCalculus.ReflectiveReplication`, `RhoCalculus.DropFreeTermination`:
  replication through quote and drop as the diagonal fixed point, and the
  bounded drop-free fragment in which no such fixed point exists.
* `RhoCalculus.QuoteMeetingPoint`: structural congruence passes through quote,
  drop and substitution; the value equality of sent names is strictly coarser
  and payload positions do not preserve it.
* `RhoCalculus.QuotedChannelInternalDecision`: a non-reflective bubble decides
  its own equality internally and has no diagonal fixed point.
* `SingleBaseSTLC.ProofByReflection`: the carved simple fragment comes with a
  sound, complete internal decision procedure on codes, used to prove
  equations by computation.
-/
