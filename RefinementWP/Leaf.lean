/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.Tactic

/-!
# The closing tactic `wrp_leaf` at the leaves of `wrp_step`

The goals at which no structural step of `wrp_step` applies are its leaves. The tactic
`wrp_leaf` closes a leaf by the first of its arms that closes it, and fails when none does.
An arm is a `macro_rules` declaration of `wrp_leaf`, so a module adds an arm for the goals of its
theory by declaring one.

The arms are tried in the order in which Lean tries the macros of one syntax: the most recently
declared first, and the arms of a later import before those of an earlier one. An arm that fails
is undone and the next one is tried. The arm of this module, which every other module of arms
imports, is therefore the last: `wrp_vcgen` followed by `grind` on each verification condition.

## Main definitions

* `wrp_leaf`: the closing tactic at a leaf of `wrp_step`, extended by `macro_rules`.
-/

public meta section

namespace RefinementWP

/--
`wrp_leaf` closes a goal by the first of its arms that closes it, and fails when none does. The
arms are the `macro_rules` declarations of `wrp_leaf`, tried from the most recently declared to
the first one. The first arm, declared with the tactic and so tried last, is `wrp_vcgen` without
equations followed by `grind` on each verification condition; it applies to a goal
`Refines ⊤ γ eps c a Q` whose programs need no unfolding.

`wrp_step` calls `wrp_leaf` at the goals where no structural step applies.
-/
syntax (name := wrpLeaf) "wrp_leaf" : tactic

macro_rules
  | `(tactic| wrp_leaf) => `(tactic| (wrp_vcgen; all_goals grind))

end RefinementWP

end
