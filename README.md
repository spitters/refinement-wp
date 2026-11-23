# refinement-wp

Verified compilers, decompilers and program logics each prove that one program implements
another, and each usually defines its own simulation relation. We present a refinement relation
for any two programs with weakest-precondition transformers in Lean's `Std.WP`, in possibly
different monads and over different state spaces. It connects the weakest refinement
precondition of S. Graf's [distillery](https://github.com/sgraf812/distillery) with the
relational refinement of [CatCrypt-core](https://github.com/spitters/CatCrypt-core), including
its graded Dijkstra-monad kernel
[XDijkstra](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/XDijkstra/README.md),
and places both in CatCrypt's
[categorical framework](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Category/XCategoricalModel.lean),
in which XDijkstra is a quantale-graded relational Dijkstra monad.

## Refinement as a residual

A concretization `γ` maps abstract assertions monotonically to concrete ones, and a relation `Q`
relates concrete to abstract return values. The weakest refinement precondition
[`wrp`](RefinementWP/WRP.lean#L105) of a concrete program `c` and an abstract program `a` is the
weakest concrete assertion `P` such that `P ⊓ γ (wp a Qa) ⊑ wp c (γ.post Q Qa)` for every
abstract postcondition `Qa`. It is the residual of that meet: `P` entails `wrp` exactly when
every such inequality holds ([`wrp_intro`](RefinementWP/WRP.lean#L120),
[`wrp_transport`](RefinementWP/WRP.lean#L129)), and
[`Refines`](RefinementWP/WRP.lean#L111) is this entailment.

In categorical terms, `wrp` is the end `∫_Qa γ (wp a Qa) ⇨ wp c (γ.post Q Qa)`, the object of
natural transformations from `γ ∘ wp a` to `wp c ∘ γ.post Q` in the Heyting algebra of concrete
assertions. At the trivial precondition, refinement is the lax square
`γ ∘ wp a ≤ wp c ∘ γ.post Q` of data refinement of predicate transformers (Gardiner and Morgan,
[TCS 87, 1991](https://doi.org/10.1016/0304-3975(91)90029-2)), with `γ` as their representation
transformer ([`refines_top_iff`](RefinementWP/Compose.lean#L134)).

## Refinement squares

A refinement is a square with the abstract program on top, the concrete program at the bottom,
and on each side a concretization with a relation between return values. Squares paste
vertically, along the composite concretization and the composite relation `γ₂.relComp Q₂ Q₁`
([`Refines.vcomp_top`](RefinementWP/Compose.lean#L271),
[`Refines.vcomp`](RefinementWP/Compose.lean#L283)), when the outer concretization preserves
suprema, and binary meets in the presence of preconditions; every concretization of a state
relation preserves suprema ([`ofStateRel_supPreserving`](RefinementWP/Compose.lean#L112)). Squares
paste horizontally by sequencing when the weakest precondition of an abstract composition is the
composite of the weakest preconditions ([`Refines.bind`](RefinementWP/Compose.lean#L311)). Each
program refines itself along the identity ([`Refines.refl`](RefinementWP/Compose.lean#L151)), and a
refinement holds under a supremum of preconditions when it holds under each
([`Refines.iSup_pre`](RefinementWP/Compose.lean#L250)). Vertical pasting chains the stages of a
compiler, and horizontal pasting is compatibility with sequencing.

The sides of the squares form a category. The identity concretization with the equality relation
is a left unit of `relComp` ([`id_relComp_eqRel`](RefinementWP/Compose.lean#L171)) and a right
unit for a concretization that preserves top and bottom
([`relComp_eqRel`](RefinementWP/Compose.lean#L189)), and `relComp` is associative through an
outer concretization that preserves suprema and binary meets
([`relComp_assoc`](RefinementWP/Compose.lean#L208)). A side `(γ, R)` acts on postconditions by
the concretization `Q ↦ γ.post R Q` ([`conjoint`](RefinementWP/Compose.lean#L385)), which preserves
suprema when `γ` does ([`conjoint_supPreserving`](RefinementWP/Compose.lean#L391)) and sends the
composite side to the composite action
([`comp_post_relComp`](RefinementWP/Compose.lean#L364)).

## Abstractions and adjoints

A concretization between complete lattices has an abstraction, its left adjoint, exactly when it
preserves all infima
([`infPreserving_iff_exists_abstraction`](RefinementWP/Galois.lean#L155); P. and R. Cousot,
[J. Logic Programming 13, 1992](https://doi.org/10.1016/0743-1066(92)90030-7), §4.2.2,
Propositions 6 and 7), and a right adjoint exactly when it preserves all suprema
([`supPreserving_iff_exists_rightAdjoint`](RefinementWP/Galois.lean#L160)). Adjoints compose
along composite concretizations ([`IsAbstraction.comp`](RefinementWP/Galois.lean#L173),
[`IsRightAdjoint.comp`](RefinementWP/Galois.lean#L179)). For a state relation, the existential
concretization has the universal concretization of the converse relation as right adjoint
([`ofStateRel_isRightAdjoint`](RefinementWP/Galois.lean#L196)), and the image is the abstraction of
the universal concretization ([`ofStateRelAll_isAbstraction`](RefinementWP/Galois.lean#L206)), as
in R.-J. Back and J. von Wright,
[Formal Aspects of Computing 12, 2000](https://doi.org/10.1007/s001650070008), §2.5 and Lemma 4.

## Separating refinement

When assertions have a separating conjunction `∗` with a right adjoint `-∗`
([`SepAssertion`](RefinementWP/Sep.lean#L107)), the separating weakest refinement precondition
[`swrp`](RefinementWP/Sep.lean#L194) replaces the Heyting residual by the magic wand. Where `∗` is
the meet, `swrp` is `wrp` ([`swrp_eq_wrp`](RefinementWP/Sep.lean#L356)). When the weakest
precondition of the concrete program frames, a refinement holds beside every disjoint assertion
([`swrp_frame`](RefinementWP/Sep.lean#L241)). Separating refinements paste vertically when the outer
concretization preserves suprema and is lax at the inner precondition and oplax at the inner return
relation with respect to `∗` ([`swrp_vcomp`](RefinementWP/Sep.lean#L320)).

The frame closure [`fwp`](RefinementWP/Sep.lean#L410) of a weakest precondition quantifies over
frames: `P` entails `fwp c Q` exactly when `P ∗ F` entails `wp c (Q ∗ F)` for every frame `F`
([`le_fwp_iff`](RefinementWP/Sep.lean#L417)), the frame-quantified triple of Birkedal, Reus,
Schwinghammer and Yang ([ICALP 2008](https://doi.org/10.1007/978-3-540-70583-3_29), Definition 1).
Every program frames every resource at the frame closure
([`fwp_frame`](RefinementWP/Sep.lean#L435)), so separating refinement at the frame closure needs no
hypothesis on the program ([`swrp_frame_fwp`](RefinementWP/Sep.lean#L459)). A transformer below the
weakest precondition that is local in the sense of Yang and O'Hearn (FoSSaCS 2002, §5.1) is below
the frame closure ([`le_fwp_of_frames`](RefinementWP/Sep.lean#L441)); this is the order-theoretic
form, for one program, of the universal property of Li, Doenges and Azevedo de Amorim
([arXiv:2611.08685](https://arxiv.org/abs/2611.08685), Theorem 6.11). The frame closure is Lean's
`PredTrans.frameClosure` at separation from a frame
([`fwp_eq_frameClosure`](RefinementWP/Sep.lean#L549)).

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
