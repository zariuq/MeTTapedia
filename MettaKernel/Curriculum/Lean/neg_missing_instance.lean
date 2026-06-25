-- NEGATIVE: instance resolution FAILS when no instance exists for the type.
class Foo (α : Type) where bar : α → Nat
def useFoo {α : Type} [Foo α] (a : α) : Nat := Foo.bar a
#eval useFoo "no Foo String instance exists"
