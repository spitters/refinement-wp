# refinement-wp

Programs whose weakest preconditions are given by Lean's `Std.WP` are the horizontal arrows of a
thin double category of refinements. A vertical arrow relates the assertions and values of two
levels of abstraction, possibly in different monads, and a square states that the program at the
bottom refines the program on top. Squares paste vertically, which chains the stages of a
compiler, and horizontally, which is sequencing. The weakest precondition is a double functor
into a double category of predicate transformers and is full on squares, so a refinement is an
inequality of transformers.

This package has the refinement judgement, its pasting laws and its proof automation, and needs
only Lean's standard library. The double categories, which use Mathlib, are in
[CatCrypt-core](https://github.com/spitters/CatCrypt-core).

## The refinement square

A vertical arrow `(γ, R)` from an abstract to a concrete level has a
[concretization](RefinementWP/WRP.lean#L63) `γ`, a monotone map from abstract to concrete
assertions, a map of exception postconditions, and a relation `R` from concrete to abstract
values. The concretization of a postcondition `Q` along `R`,
[`γ.post R Q`](RefinementWP/WRP.lean#L75), holds at a concrete value related by `R` to an
abstract value at which `γ Q` holds. A square has an abstract program `a` on top and a concrete
program `c` at the bottom:

```math
\begin{array}{ccc}
X_a & \xrightarrow{\quad a \quad} & Y_a \\
{\scriptstyle (\gamma, R)}\big\downarrow & \Downarrow & \big\downarrow{\scriptstyle (\gamma, S)} \\
X_c & \xrightarrow[\quad c \quad]{} & Y_c
\end{array}
```

It holds when, for inputs related by `R` and every abstract postcondition `Q`,
`R x_c x_a ⊓ γ (wp (a x_a) Q) ⊑ wp (c x_c) (γ.post S Q)`. For two programs under a precondition
`P`, this inequality is the [refinement](RefinementWP/WRP.lean#L111) of `a` by `c`. The weakest
such `P` is the [weakest refinement precondition](RefinementWP/WRP.lean#L105) of S. Graf's
[distillery](https://github.com/sgraf812/distillery), the residual of the meet: a refinement is
[introduced](RefinementWP/WRP.lean#L120) by checking every abstract postcondition and
[used](RefinementWP/WRP.lean#L129) by transporting one.

## Pasting

```math
\begin{array}{ccccc}
\bullet & \xrightarrow{\; a_1 \;} & \bullet & \xrightarrow{\; a_2 \;} & \bullet \\
\big\downarrow & \Downarrow & \big\downarrow & \Downarrow & \big\downarrow \\
\bullet & \xrightarrow{\; b_1 \;} & \bullet & \xrightarrow{\; b_2 \;} & \bullet \\
\big\downarrow & \Downarrow & \big\downarrow & \Downarrow & \big\downarrow \\
\bullet & \xrightarrow[\; c_1 \;]{} & \bullet & \xrightarrow[\; c_2 \;]{} & \bullet
\end{array}
```

Squares paste [vertically](RefinementWP/Compose.lean#L271), along the composite concretization and
the composite relation, when the outer concretization preserves suprema, and
[under preconditions](RefinementWP/Compose.lean#L283) when it also preserves binary meets. Every
[concretization of a state relation](RefinementWP/Compose.lean#L112) preserves suprema. Squares paste
[horizontally](RefinementWP/Compose.lean#L311) by sequencing when the weakest precondition of the
abstract sequence is below the composite of the weakest preconditions of its parts. This holds
when the abstract monad is [exact](RefinementWP/Exact.lean#L46): the weakest preconditions of
`pure x` and of `x >>= f` are given by equations, not only bounded from below. The monads of `Std.WP` and the monotone predicate
transformers are exact. In the fibrational setting of Aguirre, Katsumata and Kura
([MSCS 32(4), 2022](https://doi.org/10.1017/S0960129522000330), Theorem 6), the lower bounds hold
for every monad lifting and are equalities exactly when the lifting is Cartesian.

Every program [refines itself](RefinementWP/Compose.lean#L151) along the identity, and a refinement
[holds under a supremum](RefinementWP/Compose.lean#L250) of preconditions when it holds under each.
The vertical arrows form a category: the identity is a [left](RefinementWP/Compose.lean#L171) and a
[right](RefinementWP/Compose.lean#L189) unit, and composition is
[associative](RefinementWP/Compose.lean#L208) through an outer concretization that preserves suprema
and binary meets.

In CatCrypt-core, a [level](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPDouble.lean#L66)
is a monad with an exact weakest precondition and a Heyting algebra of assertions. Families of levels
form a [thin double category](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPLevels.lean#L210)
whose squares are exactly the [families of refinements](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPDouble.lean#L138)
above. The construction applies to any family of
[levels whose programs form a category](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPLevels.lean#L64)
with a strict weakest precondition, such as quantum channels and relational semantics.

## Squares of predicate transformers

A vertical arrow `f = (γ, R)` acts on postconditions by its
[conjoint](RefinementWP/Compose.lean#L385) `f* : Q ↦ γ.post R Q`, which
[preserves suprema](RefinementWP/Compose.lean#L391) when `γ` does and sends composite arrows to
[composite conjoints](RefinementWP/Compose.lean#L364). Predicate transformers with these vertical
arrows form a [thin double category](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPTransformers.lean#L275),
whose [squares](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPTransformers.lean#L225)
are inequalities of transformers:

```math
\begin{array}{ccc}
(Y_a \to \mathrm{Pred}_a) & \xrightarrow{\quad \mathrm{wp}\, a \quad} & (X_a \to \mathrm{Pred}_a) \\
{\scriptstyle g^*}\big\downarrow & \sqsubseteq & \big\downarrow{\scriptstyle f^*} \\
(Y_c \to \mathrm{Pred}_c) & \xrightarrow[\quad \mathrm{wp}\, c \quad]{} & (X_c \to \mathrm{Pred}_c)
\end{array}
\qquad\qquad f^* \circ \mathrm{wp}\, a \;\sqsubseteq\; \mathrm{wp}\, c \circ g^*
```

The weakest precondition is a [thin double functor](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPLevels.lean#L221)
from refinement squares to these squares, and it is
[full on squares](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPLevels.lean#L233):
a family of refinements is exactly an
[inequality of transformers](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPTransformers.lean#L300).
A concretization has an [abstraction](RefinementWP/Galois.lean#L155) exactly when it preserves
infima and a [right adjoint](RefinementWP/Galois.lean#L160) exactly when it preserves suprema. The
conjoint `f*` therefore has a right adjoint `f*ʳ`, and a square is the inequality
`wp a ⊑ f*ʳ ∘ wp c ∘ g*`: the abstract program is below the concrete program between encoding the
postcondition and decoding the precondition
([transformers](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPTransformers.lean#L285),
[levels](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPDouble.lean#L154)).

## Special cases

At the trivial precondition, a refinement is the data refinement of predicate transformers of
Gardiner and Morgan ([TCS 87, 1991](https://doi.org/10.1016/0304-3975(91)90029-2)), with `γ` as their
representation transformer ([`refines_top_iff`](RefinementWP/Compose.lean#L134)). When the weakest
precondition of `c` is that of a step relation, refinement of a partial state transformer by `c` is
[forward simulation](RefinementWP/WRP.lean#L181) from related states. For a relational semantics,
the lax squares of relations, which are forward simulations, are
[exactly](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPRelSemantics.lean#L186)
the refinement squares of the demonic weakest precondition, by a
[thin double functor](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPRelSemantics.lean#L170)
that is full on squares. Along identity arrows, a square of
[quantum channels](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPLevelsQuantum.lean#L156)
is an equality of channels.

Squares of quantum channels up to an error `ε` on the expectations of effects form a
`([0, ∞], +)`-graded double category: [identities](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPGraded.lean#L119)
have grade `0`, and [vertical](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPGraded.lean#L128)
and [horizontal](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPGraded.lean#L134)
pasting add grades. When the top channel is trace preserving, a square of grade `0` is
[exactly](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/WRPGraded.lean#L212)
a refinement square.

## Separating refinement

When assertions have a separating conjunction `∗` with a right adjoint `-∗`
([`SepAssertion`](RefinementWP/Sep.lean#L107)), the
[separating weakest refinement precondition](RefinementWP/Sep.lean#L194) replaces the Heyting
residual by the magic wand, and [equals](RefinementWP/Sep.lean#L356) the weakest refinement
precondition where `∗` is the meet. When the weakest precondition of the concrete program frames, a
refinement [holds beside every disjoint assertion](RefinementWP/Sep.lean#L241). Separating
refinements [paste vertically](RefinementWP/Sep.lean#L320) when the outer concretization preserves
suprema and is lax at the inner precondition and oplax at the inner return relation with respect
to `∗`.

The [frame closure](RefinementWP/Sep.lean#L410) of a weakest precondition is the frame-quantified
triple of Birkedal, Reus, Schwinghammer and Yang
([ICALP 2008](https://doi.org/10.1007/978-3-540-70583-3_29), Definition 1): `P` entails it at `Q`
[exactly when](RefinementWP/Sep.lean#L417) `P ∗ F` entails `wp c (Q ∗ F)` for every frame `F`.
Every program [frames](RefinementWP/Sep.lean#L435) at the frame closure, so separating refinement
at the frame closure [needs no hypothesis](RefinementWP/Sep.lean#L459) on the program. A local
transformer below the weakest precondition is [below the frame closure](RefinementWP/Sep.lean#L441),
the order-theoretic form, for one program, of the universal property of Li, Doenges and Azevedo de
Amorim ([arXiv:2611.08685](https://arxiv.org/abs/2611.08685), Theorem 6.11). The frame closure is
Lean's [`PredTrans.frameClosure`](RefinementWP/Sep.lean#L549) at separation from a frame.

## Proving refinements

The tactic [`wrp_vcgen`](RefinementWP/Tactic.lean#L156) states a refinement as a
[Hoare triple](RefinementWP/Tactic.lean#L73) of the concrete program, with the weakest precondition
of the abstract program computed from [registered equations](RefinementWP/Tactic.lean#L63), and
hands it to the toolchain's `vcgen`. The tactic [`wrp_step`](RefinementWP/Step.lean#L207) decomposes a
refinement of a sequence by [registered refinements](RefinementWP/Step.lean#L98) of its calls,
reflexivity and [sequencing](RefinementWP/Step.lean#L146), and
[`wrp_steps`](RefinementWP/Step.lean#L254) repeats it.

## Instances

S. Graf's [distillery](https://github.com/sgraf812/distillery), developed concurrently, defines the
weakest refinement precondition.

In CatCrypt's [fork](https://github.com/spitters/veir-catcrypt/tree/daa74900a698b7b85246a882266bf3a6bd49523c)
of the compiler IR [VeIR](https://github.com/opencompl/veir), the interpreter's results have a
[weakest precondition](https://github.com/spitters/veir-catcrypt/blob/daa74900a698b7b85246a882266bf3a6bd49523c/Veir/Interpreter/Refinement/WRP.lean#L29)
in which undefined behavior and failure establish no postcondition. VeIR's refinement of results is
[refinement along the identity](https://github.com/spitters/veir-catcrypt/blob/daa74900a698b7b85246a882266bf3a6bd49523c/Veir/Interpreter/Refinement/WRP.lean#L80),
and its refinement of functions is, for all refining arguments,
[refinement at the concretization of memory refinement](https://github.com/spitters/veir-catcrypt/blob/daa74900a698b7b85246a882266bf3a6bd49523c/Veir/Interpreter/Refinement/WRP.lean#L188).

The [CatCrypt compiler](https://github.com/spitters/catcrypt-compiler) proves its passes and its
correspondences between source and machine code as lax squares of relations, and these are
[refinement squares](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/RefinementSquares.lean#L82).
The soundness of a certified pass chain is
[vertical pasting](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/RefinementSquares.lean#L128)
of the refinement squares of its steps, and a machine block that corresponds to an abstract step
[refines it](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/RefinementSquares.lean#L349).
The `RustM` monad of hax and Aeneas is [exact](https://github.com/spitters/catcrypt-compiler/blob/master/HaxAscent/RustSemantics/RustMLevel.lean#L71),
so `RustM` code is a level. A square with a Lean specification on top and `RustM` code at the bottom
is a [total-correctness triple](https://github.com/spitters/catcrypt-compiler/blob/master/HaxAscent/RustSemantics/RustMLevel.lean#L162)
of the code, and such a square gives the
[correspondence](https://github.com/spitters/catcrypt-compiler/blob/master/HaxAscent/RustSemantics/RustMLevel.lean#L202)
of the compiled code with the specification. Every
[optimization level](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Quantum/Optimization/PassRefinesWP.lean#L131)
and [pass list](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Quantum/Optimization/PassRefinesWP.lean#L121)
of the quantum circuit optimizer refines its input in both directions along the identity, and the circuit compiled from a unitary tree is a
[square](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Quantum/Optimization/PassRefinesWP.lean#L143)
of the channel level.

In [CatCrypt-core](https://github.com/spitters/CatCrypt-core), the relational refinement
[`RRelPT`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRel.lean#L136)
of a partial state transformer by a step relation is
[refinement](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRP.lean#L56),
so every machine judgement of its verified decompilation is a
[refinement](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRP.lean#L68).
For transformers of state assertions with aligned exception layers, `RRelPT` and refinement
[coincide](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRP.lean#L108).
The graded Dijkstra-monad kernel
[XDijkstra](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/XDijkstra/README.md)
transfers observations along monad morphisms. With the grade forgotten, a morphism of
observations is a concretization along which the image of a program
[refines the program](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRPXDijkstra.lean#L100)
when its postcondition map lies above the concretized postconditions, which holds for every program
at the [base change](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Refinement/RRelWRPXDijkstra.lean#L252)
from state to state with failure.
