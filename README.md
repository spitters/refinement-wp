# refinement-wp

The refinement weakest precondition `wrp` over Lean's `Std.WP`, written from the published
formula of S. Graf's [distillery](https://github.com/sgraf812/distillery/blob/a5cc0e23183f92e37dfbf647a39dd8d8d30df960/Distillery/WRP.lean#L46-L49),
with one exception layer: concretizations, `wrp`, `Refines`, the introduction and transport
rules, monotone predicate transformers as abstract programs, and the characterization of the
refinement of a partial state transformer as forward simulation. The package depends only on
the Lean toolchain (v4.36.0 on this branch), so that compilers, program logics and IR interpreters can state
their refinements with one definition.

Build: `lake build RefinementWP`.
