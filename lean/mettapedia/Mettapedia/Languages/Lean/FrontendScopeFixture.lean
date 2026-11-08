import Lean

/-! A source fixture for command replay across local, global and scoped notation. -/

namespace FrontendScopeFixture

section Local
local notation "localScopeProbe" => Nat
abbrev LocalInside := localScopeProbe
end Local
abbrev localScopeProbe := Nat

section Global
notation "globalScopeProbe" => Nat
end Global
abbrev GlobalOutside := globalScopeProbe

namespace Scoped
scoped notation "scopedScopeProbe" => Nat
end Scoped

section Activation
open scoped Scoped
abbrev ScopedInside := scopedScopeProbe
end Activation
abbrev scopedScopeProbe := Nat

namespace Compound.Inner
local notation "implicitScopeProbe" => Nat
abbrev InsideImplicit := implicitScopeProbe
end Compound.Inner
abbrev implicitScopeProbe := Nat

end FrontendScopeFixture
