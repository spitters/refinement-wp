/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.Compose

/-!
# Adjoints of concretizations

In abstract interpretation a concretization `γ` comes with an abstraction `α`, its left adjoint:
`α c ⊑ a ↔ c ⊑ γ.pred a` (a Galois connection). Between complete lattices, `γ` has a left adjoint
exactly when it preserves all infima, and the adjoint is then `α c = ⨅ {a | c ⊑ γ.pred a}` (P. and
R. Cousot, "Abstract interpretation and application to logic programs", J. Logic Programming 13,
1992, §4.2.2, Propositions 6 and 7); dually, `γ` has a right adjoint exactly when it preserves all
suprema, and the adjoint is then `β c = ⨆ {a | γ.pred a ⊑ c}`. Adjoints are unique and compose
along `Concretization.comp`. For a state relation, the existential concretization has the
universal concretization of the converse relation as right adjoint, and the image is the
abstraction of the universal concretization (R.-J. Back and J. von Wright, "Encoding, decoding
and data refinement", Formal Aspects of Computing 12, 2000, §2.5 and Lemma 4).

## Main definitions

* `Concretization.IsAbstraction γ α`: `α` is a left adjoint of `γ.pred`.
* `Concretization.IsRightAdjoint γ β`: `β` is a right adjoint of `γ.pred`.
* `Concretization.InfPreserving`: `γ.pred` preserves infima of families.
* `Concretization.abstraction γ`, `Concretization.rightAdjoint γ`: the candidate adjoints, the
  infimum of the abstract assertions whose concretization is above, respectively the supremum
  of those whose concretization is below, a concrete assertion.
* `Concretization.ofStateRelAll SR`: the demonic concretization of a state relation.

## Main results

* `IsAbstraction.unique`, `IsRightAdjoint.unique`: adjoints are unique.
* `infPreserving_iff_exists_abstraction`: `γ` preserves infima if and only if it has a left
  adjoint, and `abstraction_isAbstraction` constructs it.
* `supPreserving_iff_exists_rightAdjoint`: `γ` preserves suprema if and only if it has a right
  adjoint, and `rightAdjoint_isRightAdjoint` constructs it.
* `IsAbstraction.comp`, `IsRightAdjoint.comp`, `id_isAbstraction`, `id_isRightAdjoint`: adjoints
  compose along `comp`, and the identity concretization has the identity as both adjoints.
* `ofStateRel_isRightAdjoint`: the concretization of a state relation has as right adjoint the
  demonic preimage, at `a` all `SR`-related concrete states satisfy the predicate.
* `ofStateRelAll_isAbstraction`: the image along a state relation is the abstraction of the
  demonic concretization.
-/

@[expose] public section

set_option autoImplicit false

namespace RefinementWP

open Std.WP Lean.Order

universe w

namespace Concretization

variable {CPred BPred APred : Type w} [Assertion CPred] [Assertion BPred] [Assertion APred]

/-- `α` is an abstraction of `γ`: a left adjoint of `γ.pred`, `α c ⊑ a ↔ c ⊑ γ.pred a`. -/
def IsAbstraction (γ : Concretization CPred APred) (α : CPred → APred) : Prop :=
  ∀ c a, α c ⊑ a ↔ c ⊑ γ.pred a

/-- `β` is a right adjoint of `γ.pred`: `γ.pred a ⊑ c ↔ a ⊑ β c`. -/
def IsRightAdjoint (γ : Concretization CPred APred) (β : CPred → APred) : Prop :=
  ∀ a c, γ.pred a ⊑ c ↔ a ⊑ β c

/-- `γ.pred` preserves infima of families indexed by types of universe `v'`; the inequality
    stated is the nontrivial one, the other follows from monotonicity. -/
def InfPreserving.{v'} (γ : Concretization CPred APred) : Prop :=
  ∀ {ι : Type v'} (f : ι → APred), (iInf fun i => γ.pred (f i)) ⊑ γ.pred (iInf f)

/-- The infimum of the abstract assertions whose concretization is above `c`. -/
noncomputable def abstraction (γ : Concretization CPred APred) (c : CPred) : APred :=
  iInf fun a : {a : APred // c ⊑ γ.pred a} => a.1

/-- The supremum of the abstract assertions whose concretization is below `c`. -/
noncomputable def rightAdjoint (γ : Concretization CPred APred) (c : CPred) : APred :=
  iSup fun a : {a : APred // γ.pred a ⊑ c} => a.1

variable {γ : Concretization CPred APred}

/-- The unit of an abstraction: `c` is below the concretization of its abstraction. -/
theorem IsAbstraction.le_pred {α : CPred → APred} (h : γ.IsAbstraction α) (c : CPred) :
    c ⊑ γ.pred (α c) :=
  (h c (α c)).1 PartialOrder.rel_refl

/-- The counit of a right adjoint: the concretization of `β c` is below `c`. -/
theorem IsRightAdjoint.pred_le {β : CPred → APred} (h : γ.IsRightAdjoint β) (c : CPred) :
    γ.pred (β c) ⊑ c :=
  (h (β c) c).2 PartialOrder.rel_refl

/-- Abstractions are unique. -/
theorem IsAbstraction.unique {α₁ α₂ : CPred → APred} (h₁ : γ.IsAbstraction α₁)
    (h₂ : γ.IsAbstraction α₂) : α₁ = α₂ :=
  funext fun c => PartialOrder.rel_antisymm ((h₁ _ _).2 (h₂.le_pred c)) ((h₂ _ _).2 (h₁.le_pred c))

/-- Right adjoints are unique. -/
theorem IsRightAdjoint.unique {β₁ β₂ : CPred → APred} (h₁ : γ.IsRightAdjoint β₁)
    (h₂ : γ.IsRightAdjoint β₂) : β₁ = β₂ :=
  funext fun c => PartialOrder.rel_antisymm ((h₂ _ _).1 (h₁.pred_le c)) ((h₁ _ _).1 (h₂.pred_le c))

/-- A concretization with an abstraction preserves infima of families of every universe. -/
theorem IsAbstraction.infPreserving.{v'} {α : CPred → APred} (h : γ.IsAbstraction α) :
    γ.InfPreserving.{_, v'} := by
  intro ι f
  apply (h _ _).1
  apply le_iInf
  intro i
  exact (h _ _).2 (iInf_le (fun i => γ.pred (f i)) i)

/-- A concretization with a right adjoint preserves suprema of families of every universe. -/
theorem IsRightAdjoint.supPreserving.{v'} {β : CPred → APred} (h : γ.IsRightAdjoint β) :
    γ.SupPreserving.{_, v'} := by
  intro ι f
  apply (h _ _).2
  apply iSup_le
  intro i
  exact (h _ _).1 (le_iSup (fun i => γ.pred (f i)) i)

/-- A concretization that preserves infima of families in the universe of its assertions has
    `abstraction` as abstraction. -/
theorem abstraction_isAbstraction (h : γ.InfPreserving.{_, w}) :
    γ.IsAbstraction γ.abstraction := by
  intro c a
  constructor
  · intro hca
    refine PartialOrder.rel_trans ?_ (γ.pred_mono hca)
    refine PartialOrder.rel_trans ?_ (h _)
    apply le_iInf
    intro x
    exact x.2
  · intro hca
    exact iInf_le (fun x : {a : APred // c ⊑ γ.pred a} => x.1) ⟨a, hca⟩

/-- A concretization that preserves suprema of families in the universe of its assertions has
    `rightAdjoint` as right adjoint. -/
theorem rightAdjoint_isRightAdjoint (h : γ.SupPreserving.{_, w}) :
    γ.IsRightAdjoint γ.rightAdjoint := by
  intro a c
  constructor
  · intro hac
    exact le_iSup (fun x : {a : APred // γ.pred a ⊑ c} => x.1) ⟨a, hac⟩
  · intro hac
    refine PartialOrder.rel_trans (γ.pred_mono hac) ?_
    refine PartialOrder.rel_trans (h _) ?_
    apply iSup_le
    intro x
    exact x.2

/-- A concretization preserves infima if and only if it has an abstraction. -/
theorem infPreserving_iff_exists_abstraction :
    γ.InfPreserving.{_, w} ↔ ∃ α, γ.IsAbstraction α :=
  ⟨fun h => ⟨_, abstraction_isAbstraction h⟩, fun ⟨_, h⟩ => h.infPreserving⟩

/-- A concretization preserves suprema if and only if it has a right adjoint. -/
theorem supPreserving_iff_exists_rightAdjoint :
    γ.SupPreserving.{_, w} ↔ ∃ β, γ.IsRightAdjoint β :=
  ⟨fun h => ⟨_, rightAdjoint_isRightAdjoint h⟩, fun ⟨_, h⟩ => h.supPreserving⟩

/-- The identity concretization has the identity as abstraction. -/
theorem id_isAbstraction : (Concretization.id (APred := APred)).IsAbstraction fun c => c :=
  fun _ _ => Iff.rfl

/-- The identity concretization has the identity as right adjoint. -/
theorem id_isRightAdjoint : (Concretization.id (APred := APred)).IsRightAdjoint fun c => c :=
  fun _ _ => Iff.rfl

/-- Abstractions compose: abstract along `γ₂`, then along `γ₁`. -/
theorem IsAbstraction.comp {γ₂ : Concretization CPred BPred} {γ₁ : Concretization BPred APred}
    {α₂ : CPred → BPred} {α₁ : BPred → APred} (h₂ : γ₂.IsAbstraction α₂)
    (h₁ : γ₁.IsAbstraction α₁) : (γ₂.comp γ₁).IsAbstraction fun c => α₁ (α₂ c) :=
  fun c a => (h₁ (α₂ c) a).trans (h₂ c (γ₁.pred a))

/-- Right adjoints compose: the right adjoint of `γ₂`, then that of `γ₁`. -/
theorem IsRightAdjoint.comp {γ₂ : Concretization CPred BPred} {γ₁ : Concretization BPred APred}
    {β₂ : CPred → BPred} {β₁ : BPred → APred} (h₂ : γ₂.IsRightAdjoint β₂)
    (h₁ : γ₁.IsRightAdjoint β₁) : (γ₂.comp γ₁).IsRightAdjoint fun c => β₁ (β₂ c) :=
  fun a c => (h₂ (γ₁.pred a) c).trans (h₁ a (β₂ c))

end Concretization

namespace Concretization

/-- The demonic concretization of a state relation `SR`: a concrete state satisfies the image
    of `P` when every `SR`-related abstract state satisfies `P`. -/
def ofStateRelAll {σ A : Type} (SR : σ → A → Prop) : Concretization (σ → Prop) (A → Prop) where
  pred P s := ∀ a, SR s a → P a
  pred_mono h _ hs a hsa := h a (hs a hsa)

/-- The concretization of a state relation has as right adjoint the demonic preimage: at `a`,
    every `SR`-related concrete state satisfies the predicate. -/
theorem ofStateRel_isRightAdjoint {σ A : Type} (SR : σ → A → Prop) :
    (ofStateRel SR).IsRightAdjoint fun (p : σ → Prop) (a : A) => ∀ s, SR s a → p s := by
  intro q p
  constructor
  · intro h a hq s hs
    exact h s ⟨a, hs, hq⟩
  · intro h s ⟨a, hs, hq⟩
    exact h a hq s hs

/-- The image along a state relation is the abstraction of its demonic concretization. -/
theorem ofStateRelAll_isAbstraction {σ A : Type} (SR : σ → A → Prop) :
    (ofStateRelAll SR).IsAbstraction fun (p : σ → Prop) (a : A) => ∃ s, SR s a ∧ p s := by
  intro p q
  constructor
  · intro h s hp a hs
    exact h a ⟨s, hs, hp⟩
  · intro h a ⟨s, hs, hp⟩
    exact h s hp a hs

end Concretization

end RefinementWP
