# refinement-wp

Refinement of programs over Lean's `Std.WP`. A concrete program refines an abstract program under
a precondition when every weakest-precondition fact of the abstract program, carried to concrete
states by a concretization and met with the precondition, entails the corresponding fact of the
concrete program, with return values related by a given relation. The judgement is the
refinement weakest precondition of S. Graf's
[distillery](https://github.com/sgraf812/distillery/blob/a5cc0e23183f92e37dfbf647a39dd8d8d30df960/Distillery/WRP.lean#L46-L49),
with one exception layer. At the trivial precondition it is data refinement by forward
simulation: the concretization of the abstract weakest precondition lies below the concrete one.

## Main results

The refinement weakest precondition is
[`wrp`](RefinementWP/WRP.lean#L104), and refinement under a precondition is
[`Refines`](RefinementWP/WRP.lean#L110). A refinement is established by checking each abstract
postcondition ([`wrp_intro`](RefinementWP/WRP.lean#L119)) and used by transporting one to the concrete
program ([`wrp_transport`](RefinementWP/WRP.lean#L128)).

The abstract programs are monotone predicate transformers on state predicates
([`MonoPT`](RefinementWP/WRP.lean#L140)), as in the refinement calculus. For a partial state transformer
`f`, refinement of its program by a concrete program whose weakest precondition is that of a step
relation `T` holds exactly when `T` simulates `f` forward from related states
([`refines_optD_iff`](RefinementWP/WRP.lean#L180)).
