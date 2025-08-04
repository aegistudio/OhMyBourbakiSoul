# MyOrd

For a type `α`, sometimes we may want to equip it
with an reflexive, transitive and antisymmetric
partial order relationship, or equip it with an
irreflexive, transitive and asymmetric strict
order relationship. The module `MyOrd` provides
common and abstract theorems from order theory
so that other proofs can reuse them.

To do so, one may first define `LE α` or `LT α`,
so that we may write `a ≤ b` or `a < b`, and
then define the type class of `MyPartialOrd α`
or `MyStrictOrd α`. The order relationship in
the `le` field of `LE α` or `lt` field of
`LT α` is called the the canonical order
relationship. It's a stupid idea to define
multiple different order relationship on the
same type `α` by associating multiple
instances of `LE α` or `LT α` with it. If you
read the documentation about instantiation in
Lean 4, it will tell you every instance is
considered "as good as" another. So defining
multiple instances of `LE α` or `LT α` can
really lead to anarchy in your type `α`.

If defining multiple different partial order
relation on the same type is inevitable,
it's recommend to define them on more
specific type, say `Casted₁ α` and `Casted₂ α`,
and then define `LE (Casted₁ α)` and
`LE (Casted₂ α)`, or `LT (Casted₁ α)` and
`LT (Casted₂ α)`, alongside with `MyPartialOrd`
or `MyStrictOrd` for them. And in proof, say
we would like to apply theorems on the order
on `Casted₁ α`, we cast / coerce the related
variables in the expression to `Casted₁ α`,
apply theorems, and then cast / coerce them back.

On the other hand, it's a very bad idea to allow
`LE α` incompatible with `LT α`, that is,
`a < b` is not equivalent to `(a ≤ b) ∧ (a ≠ b)`.
This violates the convention in mathematics
and inflicts cognitive burden. Again, define
order relations on specific types rather putting
incompatible orders as canonical partial and
strict orders on `α`. We offer `MyOrd.Induced`
to enable Lean to automatically induce the
compatible `a < b` for us after defining
`a ≤ b`, or vice versa.
