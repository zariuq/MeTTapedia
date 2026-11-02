import Mettapedia.Logic.TierZero.Adequacy.MM0
import Mettapedia.Logic.TierZero.Adequacy.MM0Worlds
import Mettapedia.Logic.TierZero.Adequacy.HOLPres
import Mettapedia.Logic.TierZero.Adequacy.HOLWorlds
import Mettapedia.Logic.TierZero.Adequacy.HOLEnc
import Mettapedia.Logic.TierZero.Adequacy.HOLOps

/-!
# Adequacy of the tier-0 kernel for proof systems

* `Adequacy.MM0`: Mettapedia's MM0 kernel. Bound variables are scope formals and regular
  variables are names over their dependencies' names, so the names in an encoded term are its MM0
  support; `derivable_iff_derives` and `kernel_accepts_iff_derives`.
* `Adequacy.MM0Worlds`: MM0 claims with bound variables as kernel-v2 worlds, for running the Lean
  kernel and the MeTTa kernel on identical inputs (`Controls.nfWorld`).
* `Adequacy.HOLPres`: HOL Light's kernel (`fusion.ml`) as rules, `holRules`, with its extension
  operations as rule generators. Its adequacy to Mettapedia's HOL Light specification is not yet
  proved here.
* `Adequacy.HOLWorlds`: HOL Light proofs as kernel-v2 worlds (`Controls.holWorld`: the ten
  primitive inferences, `TRUTH` from `T_DEF`, and refused controls).
* `Adequacy.HOLEnc`: the specification's HOL Light types and de Bruijn terms as kernel terms
  (`encTy`, `encDB`, `EncSet`); encoded checked terms are locally closed; the type encoding is
  injective over a signature.
* `Adequacy.HOLOps`: the kernel's `open` is the specification's beta instantiation on encoded
  terms (`openT_encDB`).
-/
