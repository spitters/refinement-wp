# refinement-wp

Verified compilers, decompilers and program logics each prove that one program implements
another, and each usually defines its own simulation relation. This package defines refinement
once, for any two programs with weakest-precondition transformers in Lean's `Std.WP`, in
possibly different monads and over different state spaces. The definition is the refinement
weakest precondition of S. Graf's [distillery](https://github.com/sgraf812/distillery).

## Refinement as a residual

A concretization `γ` maps abstract assertions monotonically to concrete ones, and a relation `Q`
relates concrete to abstract return values. The refinement weakest precondition
[`wrp`](RefinementWP/WRP.lean#L104) of a concrete program `c` and an abstract program `a` is the
weakest concrete assertion `P` such that `P ⊓ γ (wp a Qa) ⊑ wp c (γ.post Q Qa)` for every
abstract postcondition `Qa`. It is the residual of that meet: `P` entails `wrp` exactly when
every such inequality holds ([`wrp_intro`](RefinementWP/WRP.lean#L119),
[`wrp_transport`](RefinementWP/WRP.lean#L128)), and
[`Refines`](RefinementWP/WRP.lean#L110) is this entailment.

In categorical terms, `wrp` is the end `∫_Qa γ (wp a Qa) ⇨ wp c (γ.post Q Qa)`, the object of
natural transformations from `γ ∘ wp a` to `wp c ∘ γ.post Q` in the Heyting algebra of concrete
assertions. At the trivial precondition, refinement is the lax square
`γ ∘ wp a ≤ wp c ∘ γ.post Q`, the forward data refinement of Gardiner and Morgan, where `wp a`
and `wp c` are effect observations in the sense of Dijkstra monads.

## Forward simulation

Abstract programs are monotone predicate transformers, as in the refinement calculus
([`MonoPT`](RefinementWP/WRP.lean#L140)). When the weakest precondition of `c` is that of a step
relation `T`, refinement of a partial state transformer `f` by `c` is forward simulation of `f` by
`T` from related states ([`refines_optD_iff`](RefinementWP/WRP.lean#L180)).

## Relation to CatCrypt-core

In [CatCrypt-core](https://github.com/spitters/CatCrypt-core), relational refinement
[`RRelPT`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRel.lean#L136)
is a logical relation between predicate transformers. Its verified decompilation states every
machine judgement as
[`GuardedRRelPT`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/Programs.lean#L346),
the refinement of a guarded update. For a partial state transformer and a step relation, `RRelPT`
is the same forward simulation
([`rrelPT_optProg_wpRel_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/Programs.lean#L256)),
so `RRelPT`, `GuardedRRelPT` and `Refines` agree on these programs.
