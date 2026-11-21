/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.Compose

/-!
# Side conditions of pasting by instance search, and chains of refinements

Vertical pasting of refinements (`Refines.vcomp_top`) needs the outer concretization to preserve
suprema. The class `Concretization.IsSupPreserving` states this condition, with instances for the
concretization of a state relation, the identity and composites, so that instance search
discharges it. The relation `RefinesTop γ eps Q`, refinement under `⊤` with its concretization,
exception map and return relation as parameters, has a `Trans` instance, so a `calc` block chains
the refinements of successive stages.

## Main definitions

* `Concretization.IsSupPreserving`: the class form of `Concretization.SupPreserving`.
* `RefinesTop γ eps Q c a`: refinement of `a` by `c` under `⊤`.

## Main results

* Instances of `IsSupPreserving` for `ofStateRel`, `id` and `comp`.
* `RefinesTop.trans`: vertical pasting with the side condition found by instance search.
* A `Trans` instance for `RefinesTop`.
-/

@[expose] public section

set_option autoImplicit false

namespace RefinementWP

open Std.WP Lean.Order

universe u v w w'

namespace Concretization

variable {CPred BPred APred : Type w} [Assertion CPred] [Assertion BPred] [Assertion APred]

/-- `γ` preserves suprema of families indexed by types of universe `v'`: the class form of
    `SupPreserving`, for instance search. -/
class IsSupPreserving.{v'} (γ : Concretization CPred APred) : Prop where
  /-- `γ.pred` preserves suprema. -/
  sup : γ.SupPreserving.{_, v'}

/-- The concretization of a state relation preserves suprema. -/
instance {σ A : Type} (SR : σ → A → Prop) : (ofStateRel SR).IsSupPreserving.{_, 0} :=
  ⟨@fun _ f => ofStateRel_supPreserving SR f⟩

/-- The identity concretization preserves suprema. -/
instance IsSupPreserving.id.{v'} : (Concretization.id (APred := APred)).IsSupPreserving.{_, v'} :=
  ⟨fun _ => PartialOrder.rel_refl⟩

/-- A composite of concretizations that preserve suprema preserves suprema. -/
instance IsSupPreserving.comp.{v'} (γ₂ : Concretization CPred BPred)
    (γ₁ : Concretization BPred APred) [h₂ : γ₂.IsSupPreserving.{_, v'}]
    [h₁ : γ₁.IsSupPreserving.{_, v'}] : (γ₂.comp γ₁).IsSupPreserving.{_, v'} :=
  ⟨fun f => PartialOrder.rel_trans (γ₂.pred_mono (h₁.sup f)) (h₂.sup _)⟩

end Concretization

section Chains

variable {CProg BProg AProg : Type u} {CVal BVal AVal : Type v} {CPred BPred APred : Type w}
  {CE BE AE : Type w'}
  [Assertion CPred] [Assertion BPred] [Assertion APred] [Assertion CE] [Assertion BE]
  [Assertion AE]
  [WP CProg CVal CPred CE] [WP BProg BVal BPred BE] [WP AProg AVal APred AE]

/-- Refinement of `a` by `c` under `⊤`, with the concretization, the exception map and the
    return relation as parameters, so that it is a relation between programs. -/
abbrev RefinesTop (γ : Concretization CPred APred) (eps : AE → CE) (Q : CVal → AVal → CPred)
    (c : CProg) (a : AProg) : Prop :=
  Refines top γ eps c a Q

/-- Vertical pasting of refinements under `⊤`, with preservation of suprema by the outer
    concretization found by instance search. -/
theorem RefinesTop.trans [Heyting BPred] [Heyting CPred] {γ₂ : Concretization CPred BPred}
    {γ₁ : Concretization BPred APred} [γ₂.IsSupPreserving.{_, v}] {eps₂ : BE → CE}
    {eps₁ : AE → BE} {Q₂ : CVal → BVal → CPred} {Q₁ : BVal → AVal → BPred} {c : CProg}
    {b : BProg} {a : AProg} (h₂ : RefinesTop γ₂ eps₂ Q₂ c b) (h₁ : RefinesTop γ₁ eps₁ Q₁ b a) :
    RefinesTop (γ₂.comp γ₁) (fun e => eps₂ (eps₁ e)) (γ₂.relComp Q₂ Q₁) c a :=
  Refines.vcomp_top Concretization.IsSupPreserving.sup h₁ h₂

/-- Chains of refinements under `⊤` in `calc`. -/
instance [Heyting BPred] [Heyting CPred] {γ₂ : Concretization CPred BPred}
    {γ₁ : Concretization BPred APred} [γ₂.IsSupPreserving.{_, v}] {eps₂ : BE → CE}
    {eps₁ : AE → BE} {Q₂ : CVal → BVal → CPred} {Q₁ : BVal → AVal → BPred} :
    @Trans CProg BProg AProg (RefinesTop γ₂ eps₂ Q₂) (RefinesTop γ₁ eps₁ Q₁)
      (RefinesTop (γ₂.comp γ₁) (fun e => eps₂ (eps₁ e)) (γ₂.relComp Q₂ Q₁)) :=
  ⟨RefinesTop.trans⟩

/-- A chain of two refinements of monotone predicate transformers along state relations,
    pasted by `calc` with the side condition found by instance search. -/
example {σ τ A : Type} (SR₂ : σ → τ → Prop) (SR₁ : τ → A → Prop) (Q₂ : Unit → Unit → σ → Prop)
    (Q₁ : Unit → Unit → τ → Prop) (c : MonoPT σ Unit) (b : MonoPT τ Unit) (a : MonoPT A Unit)
    (h₂ : RefinesTop (Concretization.ofStateRel SR₂) (fun e : Unit => e) Q₂ c b)
    (h₁ : RefinesTop (Concretization.ofStateRel SR₁) (fun e : Unit => e) Q₁ b a) :
    RefinesTop ((Concretization.ofStateRel SR₂).comp (Concretization.ofStateRel SR₁))
      (fun e => (fun e : Unit => e) ((fun e : Unit => e) e))
      ((Concretization.ofStateRel SR₂).relComp Q₂ Q₁) c a :=
  calc RefinesTop (Concretization.ofStateRel SR₂) (fun e : Unit => e) Q₂ c b := h₂
    RefinesTop (Concretization.ofStateRel SR₁) (fun e : Unit => e) Q₁ _ a := h₁

end Chains

end RefinementWP
