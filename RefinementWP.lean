/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.WRP
public import RefinementWP.Compose
public import RefinementWP.Classes
public import RefinementWP.Tactic
public import RefinementWP.Step
public import RefinementWP.Sep

/-!
# refinement-wp

The root of the package: the refinement weakest precondition `RefinementWP.wrp` and its
refinement judgement `RefinementWP.Refines` (`RefinementWP.WRP`), their composition
(`RefinementWP.Compose`, `RefinementWP.Classes`), the tactic `wrp_vcgen`
(`RefinementWP.Tactic`), the registry `RefinesCall` with the tactics `wrp_step` and
`wrp_steps` (`RefinementWP.Step`), and the separating refinement weakest precondition
`RefinementWP.swrp` over assertions with a separating conjunction (`RefinementWP.Sep`).
-/
