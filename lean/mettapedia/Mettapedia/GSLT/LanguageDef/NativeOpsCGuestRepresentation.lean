import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSnapshot
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsCGuest

open NativeOps NativeOps.NativeC

def representation : Representation := ⟨"VibeITPKernel", NativeOpsSourceGuestSnapshot.expectedInterface, [(.word, [Char.ofNat 67, Char.ofNat 101, Char.ofNat 116, Char.ofNat 116, Char.ofNat 97, Char.ofNat 71, Char.ofNat 115, Char.ofNat 108, Char.ofNat 116, Char.ofNat 95, Char.ofNat 86, Char.ofNat 105, Char.ofNat 98, Char.ofNat 101, Char.ofNat 73, Char.ofNat 84, Char.ofNat 80, Char.ofNat 75, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110, Char.ofNat 101, Char.ofNat 108, Char.ofNat 95, Char.ofNat 65, Char.ofNat 114, Char.ofNat 114, Char.ofNat 97, Char.ofNat 121, Char.ofNat 49, Char.ofNat 86, Char.ofNat 49]), ((.ref (.named "Term")), [Char.ofNat 67, Char.ofNat 101, Char.ofNat 116, Char.ofNat 116, Char.ofNat 97, Char.ofNat 71, Char.ofNat 115, Char.ofNat 108, Char.ofNat 116, Char.ofNat 95, Char.ofNat 86, Char.ofNat 105, Char.ofNat 98, Char.ofNat 101, Char.ofNat 73, Char.ofNat 84, Char.ofNat 80, Char.ofNat 75, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110, Char.ofNat 101, Char.ofNat 108, Char.ofNat 95, Char.ofNat 65, Char.ofNat 114, Char.ofNat 114, Char.ofNat 97, Char.ofNat 121, Char.ofNat 50, Char.ofNat 86, Char.ofNat 49]), ((.ref (.named "Symbol")), [Char.ofNat 67, Char.ofNat 101, Char.ofNat 116, Char.ofNat 116, Char.ofNat 97, Char.ofNat 71, Char.ofNat 115, Char.ofNat 108, Char.ofNat 116, Char.ofNat 95, Char.ofNat 86, Char.ofNat 105, Char.ofNat 98, Char.ofNat 101, Char.ofNat 73, Char.ofNat 84, Char.ofNat 80, Char.ofNat 75, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110, Char.ofNat 101, Char.ofNat 108, Char.ofNat 95, Char.ofNat 65, Char.ofNat 114, Char.ofNat 114, Char.ofNat 97, Char.ofNat 121, Char.ofNat 51, Char.ofNat 86, Char.ofNat 49]), ((.ref (.named "Theorem")), [Char.ofNat 67, Char.ofNat 101, Char.ofNat 116, Char.ofNat 116, Char.ofNat 97, Char.ofNat 71, Char.ofNat 115, Char.ofNat 108, Char.ofNat 116, Char.ofNat 95, Char.ofNat 86, Char.ofNat 105, Char.ofNat 98, Char.ofNat 101, Char.ofNat 73, Char.ofNat 84, Char.ofNat 80, Char.ofNat 75, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110, Char.ofNat 101, Char.ofNat 108, Char.ofNat 95, Char.ofNat 65, Char.ofNat 114, Char.ofNat 114, Char.ofNat 97, Char.ofNat 121, Char.ofNat 52, Char.ofNat 86, Char.ofNat 49])]⟩

end Mettapedia.GSLT.LanguageDef.NativeOpsCGuest
