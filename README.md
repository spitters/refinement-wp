# refinement-wp

The refinement weakest precondition `wrp` over Lean's `Std.WP`, written from the published
formula of S. Graf's [distillery](https://github.com/sgraf812/distillery/blob/a5cc0e23183f92e37dfbf647a39dd8d8d30df960/Distillery/WRP.lean#L46-L49),
with one exception layer: concretizations, `wrp`, `Refines`, the introduction and transport
rules, monotone predicate transformers as abstract programs, and the characterization of the
refinement of a partial state transformer as forward simulation. The package depends only on
the Lean toolchain (v4.36.0 on this branch), so that compilers, program logics and IR interpreters can state
their refinements with one definition.

## Contents

`RefinementWP/WRP.lean`, namespace `RefinementWP`:

| Declaration | Content |
|---|---|
| `Concretization`, `Concretization.post`, `Concretization.ofStateRel` | a monotone map from abstract to concrete assertions; the concrete postcondition of a return relation; the concretization of a state relation |
| `wrp γ eps c a Q` | `⨅ Qa Ea, γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (eps Ea)`, with one exception layer `eps : AE → CE` |
| `Refines P γ eps c a Q` | `P ⊑ wrp γ eps c a Q`: the concrete program `c` refines the abstract program `a` under `P` |
| `wrp_intro`, `wrp_transport` | the introduction and elimination rules |
| `MonoPT`, `optD` | monotone predicate transformers as abstract programs, with their `WP` instance; the program of a partial state transformer |
| `refines_optD_iff` | refinement of `optD f` is forward simulation of `f` by the concrete step relation |

At `P = ⊤`, `Refines` is the lax square `γ ∘ wp a ≤ wp c ∘ γ.post Q` of data refinement by
forward simulation.

## Use

```lean
require «refinement-wp» from git "https://github.com/spitters/refinement-wp" @ "main"
```

| Branch | Lean |
|---|---|
| `main` | v4.35.0 |
| `lean-4.36` | v4.36.0 |

Build with `lake build`.

## Relation to distillery

distillery has no licence file, so this package contains no distillery code. It restates the
formula and the statement shapes of `wrp`, `wrp_intro` and `wrp_transport`, restricted to one
exception layer, with its own proofs. When distillery is licensed and builds on a release
toolchain, the definitions here are meant to be replaced by its own.

## Licence

MIT, see [LICENSE](LICENSE).
