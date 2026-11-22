# refinement-wp

Verified compilers, decompilers and program logics each prove that one program implements
another, and each usually defines its own simulation relation. We present a refinement relation
for any two programs with weakest-precondition transformers in Lean's `Std.WP`, in possibly
different monads and over different state spaces. It connects the refinement weakest
precondition of S. Graf's [distillery](https://github.com/sgraf812/distillery) with the
relational refinement of [CatCrypt-core](https://github.com/spitters/CatCrypt-core), including
its graded Dijkstra-monad kernel
[XDijkstra](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/XDijkstra/README.md),
and places both in CatCrypt's
[categorical framework](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Category/XCategoricalModel.lean),
in which XDijkstra is a quantale-graded relational Dijkstra monad.

## Refinement as a residual

A concretization `γ` maps abstract assertions monotonically to concrete ones, and a relation `Q`
relates concrete to abstract return values. The refinement weakest precondition
[`wrp`](RefinementWP/WRP.lean#L105) of a concrete program `c` and an abstract program `a` is the
weakest concrete assertion `P` such that `P ⊓ γ (wp a Qa) ⊑ wp c (γ.post Q Qa)` for every
abstract postcondition `Qa`. It is the residual of that meet: `P` entails `wrp` exactly when
every such inequality holds ([`wrp_intro`](RefinementWP/WRP.lean#L120),
[`wrp_transport`](RefinementWP/WRP.lean#L129)), and
[`Refines`](RefinementWP/WRP.lean#L111) is this entailment.

In categorical terms, `wrp` is the end `∫_Qa γ (wp a Qa) ⇨ wp c (γ.post Q Qa)`, the object of
natural transformations from `γ ∘ wp a` to `wp c ∘ γ.post Q` in the Heyting algebra of concrete
assertions. At the trivial precondition, refinement is the lax square
`γ ∘ wp a ≤ wp c ∘ γ.post Q`, the forward data refinement of Gardiner and Morgan, where `wp a`
and `wp c` are effect observations in the sense of Dijkstra monads
([`refines_top_iff`](RefinementWP/Compose.lean#L126)).

## Pasting

Refinements compose as 2-cells. Along a chain of programs `a`, `b`, `c` with concretizations
`γ₁` and `γ₂`, the two squares paste vertically to a refinement of `a` by `c` along the
composite concretization ([`Refines.vcomp_top`](RefinementWP/Compose.lean#L168)). The outer
concretization must preserve suprema; every concretization of a state relation does
([`ofStateRel_supPreserving`](RefinementWP/Compose.lean#L104)). Each program refines itself along
the identity ([`Refines.refl`](RefinementWP/Compose.lean#L143)). When the weakest precondition of
an abstract composition is the composite of the weakest preconditions, refinement of a program
and of its continuations gives refinement of their sequential composition
([`Refines.bind`](RefinementWP/Compose.lean#L208)). Vertical pasting chains the stages of a
compiler, and horizontal pasting is compatibility with sequencing.

## Forward simulation

Abstract programs are monotone predicate transformers, as in the refinement calculus
([`MonoPT`](RefinementWP/WRP.lean#L141)). When the weakest precondition of `c` is that of a step
relation `T`, refinement of a partial state transformer `f` by `c` is forward simulation of `f` by
`T` from related states ([`refines_optD_iff`](RefinementWP/WRP.lean#L181)).

## Refinement in VeIR

In CatCrypt's [fork](https://github.com/spitters/veir-catcrypt/tree/daa74900a698b7b85246a882266bf3a6bd49523c)
of [VeIR](https://github.com/opencompl/veir), a compiler IR in Lean, the interpreter's results have a
[weakest precondition](https://github.com/spitters/veir-catcrypt/blob/daa74900a698b7b85246a882266bf3a6bd49523c/Veir/Interpreter/Refinement/WRP.lean#L29)
in which undefined behavior and failure establish no postcondition. VeIR's refinement of a source
result by a target result is refinement in the sense of `wrp` along the identity
([`interp_isRefinedBy_iff_refines`](https://github.com/spitters/veir-catcrypt/blob/daa74900a698b7b85246a882266bf3a6bd49523c/Veir/Interpreter/Refinement/WRP.lean#L80)).
VeIR's refinement of functions is, for all refining arguments, `wrp` refinement of their state
transformers at the concretization of memory refinement
([`functionOp_isRefinedBy_iff_refines`](https://github.com/spitters/veir-catcrypt/blob/daa74900a698b7b85246a882266bf3a6bd49523c/Veir/Interpreter/Refinement/WRP.lean#L188)).

## Relation to CatCrypt-core

In [CatCrypt-core](https://github.com/spitters/CatCrypt-core), relational refinement
[`RRelPT`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRel.lean#L136)
is a logical relation between predicate transformers. Its verified decompilation states every
machine judgement as
[`GuardedRRelPT`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/Programs.lean#L346),
the refinement of a guarded update. `RRelPT` of a partial state transformer by a step relation is
refinement in the sense of `wrp`
([`rrelPT_optProg_iff_refines`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRP.lean#L56)),
so every machine judgement of the decompilation is a `wrp` refinement
([`guardedRRelPT_iff_refines`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRP.lean#L68)).
For transformers of state assertions with aligned exception layers, `RRelPT` and `Refines`
coincide ([`rrelPT_iff_refines`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRP.lean#L108)).

## Relation to XDijkstra

XDijkstra observes a program as a graded predicate transformer and transfers observations along
monad morphisms. Read through `Std.WP` with the grade forgotten, a morphism of observations is a
concretization, and when its postcondition map lies above the concretized postconditions, the
image of a program refines the program along it
([`refines_of_wpHom`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRPXDijkstra.lean#L100)).
At the base change from state to state with failure the condition holds for every program
([`refines_thetaX`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRPXDijkstra.lean#L252)).
For an observation pulled back along a monad morphism, a program and its image refine each other
along the identity
([`refines_pullback_image`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRPXDijkstra.lean#L131),
[`refines_image_pullback`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRPXDijkstra.lean#L140)).
