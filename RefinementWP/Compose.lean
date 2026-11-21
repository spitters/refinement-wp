/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.WRP
public import Std.WP

/-!
# Pasting of refinement squares

A refinement `Refines top γ eps c a Q` is a lax square `γ ∘ wp a ≤ wp c ∘ γ.post Q` of forward
data refinement. This module proves the lax-square form of `Refines top`, the vertical pasting
of squares along composite concretizations (chains of refinement stages), the identity square,
and horizontal pasting along `bind` (compatibility of refinement with sequencing).

## Main definitions

* `Concretization.id`: the identity concretization.
* `Concretization.comp γ₂ γ₁`: the concretization `γ₂.pred ∘ γ₁.pred`.
* `Concretization.relComp γ₂ Q₂ Q₁`: the composite return relation, at `cv av` the supremum
  over `bv` of `Q₂ cv bv` met with `γ₂.pred (Q₁ bv av)`.
* `Concretization.SupPreserving`, `Concretization.MeetPreserving`: `γ.pred` preserves suprema
  of families, respectively binary meets (each stated as the nontrivial inequality).
* `eqRel`: the equality return relation.

## Main results

* `refines_top_iff`: `Refines top` is the lax square.
* `Concretization.post_comp_le`: the postcondition of a composite square is below the
  postcondition of the composite concretization and return relation.
* `Refines.vcomp_top`, `Refines.vcomp`: vertical pasting, without and with preconditions.
* `Concretization.ofStateRel_supPreserving`, `Concretization.ofStateRel_meetPreserving`: the
  concretization of a state relation preserves suprema, and binary meets when the relation is
  functional.
* `Refines.refl`: reflexivity at the identity concretization.
* `Refines.bind`: horizontal pasting along `bind` of `WPMonad` instances.
-/

@[expose] public section

set_option autoImplicit false

namespace RefinementWP

open Std.WP Lean.Order

universe u v w w'

namespace Concretization

variable {CPred BPred APred : Type w} [Assertion CPred] [Assertion BPred] [Assertion APred]

/-- The identity concretization. -/
def id : Concretization APred APred where
  pred p := p
  pred_mono h := h

/-- The composite concretization: `γ₁` from `APred` to `BPred`, then `γ₂` to `CPred`. -/
def comp (γ₂ : Concretization CPred BPred) (γ₁ : Concretization BPred APred) :
    Concretization CPred APred where
  pred p := γ₂.pred (γ₁.pred p)
  pred_mono h := γ₂.pred_mono (γ₁.pred_mono h)

/-- The composite return relation through the outer concretization `γ₂`: at `cv av` it is the
    supremum over `bv` of `Q₂ cv bv` met with `γ₂.pred (Q₁ bv av)`. -/
noncomputable def relComp (γ₂ : Concretization CPred BPred) {CVal BVal AVal : Type v}
    (Q₂ : CVal → BVal → CPred) (Q₁ : BVal → AVal → BPred) : CVal → AVal → CPred :=
  fun cv av => iSup fun bv => meet (Q₂ cv bv) (γ₂.pred (Q₁ bv av))

/-- `γ.pred` preserves suprema of families indexed by types of universe `v`; the inequality
    stated is the nontrivial one, the other follows from monotonicity. -/
def SupPreserving.{v'} (γ : Concretization CPred APred) : Prop :=
  ∀ {ι : Type v'} (f : ι → APred), γ.pred (iSup f) ⊑ iSup fun i => γ.pred (f i)

/-- `γ.pred` preserves binary meets; the inequality stated is the nontrivial one, the other
    follows from monotonicity. -/
def MeetPreserving (γ : Concretization CPred APred) : Prop :=
  ∀ p q : APred, meet (γ.pred p) (γ.pred q) ⊑ γ.pred (meet p q)

/-- The postcondition of the pasted square is below the postcondition of the composite
    concretization at the composite return relation. -/
theorem post_comp_le [Heyting CPred] {γ₂ : Concretization CPred BPred}
    {γ₁ : Concretization BPred APred} {CVal BVal AVal : Type v} (hsup : γ₂.SupPreserving.{_, v})
    (Q₂ : CVal → BVal → CPred) (Q₁ : BVal → AVal → BPred) (Qa : AVal → APred) :
    γ₂.post Q₂ (γ₁.post Q₁ Qa) ⊑ (γ₂.comp γ₁).post (γ₂.relComp Q₂ Q₁) Qa := by
  intro cv
  apply iSup_le
  intro bv
  refine PartialOrder.rel_trans (meet_mono_right (hsup _)) ?_
  apply meet_le_of_le_himp_comm
  apply iSup_le
  intro av
  apply le_himp
  refine PartialOrder.rel_trans ?_ (le_iSup _ av)
  apply le_meet
  · refine PartialOrder.rel_trans ?_ (le_iSup _ bv)
    exact meet_mono_right (γ₂.pred_mono (meet_le_left _ _))
  · exact meet_le_of_right_le (γ₂.pred_mono (meet_le_right _ _))

/-- The concretization of a state relation preserves suprema. -/
theorem ofStateRel_supPreserving {σ A : Type} (SR : σ → A → Prop) :
    (ofStateRel SR).SupPreserving.{_, 0} := by
  intro ι f s hs
  simp only [ofStateRel, iSup_apply, iSup_prop_eq_exists] at hs ⊢; grind

/-- The concretization of a functional state relation preserves binary meets. -/
theorem ofStateRel_meetPreserving {σ A : Type} (SR : σ → A → Prop)
    (hfun : ∀ s a a', SR s a → SR s a' → a = a') :
    (ofStateRel SR).MeetPreserving := by
  intro p q s hs
  simp only [ofStateRel, meet_apply, meet_prop_eq_and] at hs ⊢; grind

end Concretization

section Square

variable {CProg AProg : Type u} {CVal AVal : Type v} {CPred APred : Type w} {CE AE : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CE] [Assertion AE]
  [WP CProg CVal CPred CE] [WP AProg AVal APred AE]

/-- `Refines top` is the lax square: each concretized abstract `wp` fact entails the concrete
    `wp` fact at the concrete postcondition. -/
theorem refines_top_iff [Heyting CPred] {γ : Concretization CPred APred} {eps : AE → CE}
    {c : CProg} {a : AProg} {Q : CVal → AVal → CPred} :
    Refines top γ eps c a Q ↔
      ∀ (Qa : AVal → APred) (Ea : AE), γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (eps Ea) := by
  constructor
  · intro h Qa Ea
    exact PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl)
      (wrp_transport h Qa Ea)
  · intro h
    exact wrp_intro fun Qa Ea => meet_le_of_right_le (h Qa Ea)

/-- The equality return relation. -/
noncomputable def eqRel : CVal → CVal → CPred :=
  fun v v' => CompleteLattice.ofProp (v = v')

/-- Reflexivity: every program refines itself at the identity concretization, the identity
    exception map and the equality return relation, under every precondition. -/
theorem Refines.refl (P : CPred) (c : CProg) :
    Refines P Concretization.id (fun e : CE => e) c c (eqRel (CPred := CPred)) := by
  apply wrp_intro
  intro Qa Ea
  refine PartialOrder.rel_trans (meet_le_right _ _) (WP.wp_consequence _ _ _ _ ?_)
  intro v
  refine PartialOrder.rel_trans ?_ (le_iSup _ v)
  exact le_meet _ _ _ (le_ofProp _ _ rfl) PartialOrder.rel_refl

end Square

section Vertical

variable {CProg BProg AProg : Type u} {CVal BVal AVal : Type v} {CPred BPred APred : Type w}
  {CE BE AE : Type w'}
  [Assertion CPred] [Assertion BPred] [Assertion APred] [Assertion CE] [Assertion BE]
  [Assertion AE]
  [WP CProg CVal CPred CE] [WP BProg BVal BPred BE] [WP AProg AVal APred AE]
  {γ₂ : Concretization CPred BPred} {γ₁ : Concretization BPred APred}
  {eps₂ : BE → CE} {eps₁ : AE → BE} {c : CProg} {b : BProg} {a : AProg}
  {Q₂ : CVal → BVal → CPred} {Q₁ : BVal → AVal → BPred}

/-- Vertical pasting of lax squares: if `b` refines `a` along `γ₁` and `c` refines `b` along
    `γ₂`, then `c` refines `a` along the composite concretization, exception map and return
    relation, when `γ₂` preserves suprema. -/
theorem Refines.vcomp_top [Heyting BPred] [Heyting CPred] (hsup : γ₂.SupPreserving.{_, v})
    (h₁ : Refines top γ₁ eps₁ b a Q₁) (h₂ : Refines top γ₂ eps₂ c b Q₂) :
    Refines top (γ₂.comp γ₁) (fun e => eps₂ (eps₁ e)) c a (γ₂.relComp Q₂ Q₁) := by
  rw [refines_top_iff] at h₁ h₂ ⊢
  intro Qa Ea
  exact PartialOrder.rel_trans (γ₂.pred_mono (h₁ Qa Ea))
    (PartialOrder.rel_trans (h₂ _ _)
      (WP.wp_consequence _ _ _ _ (Concretization.post_comp_le hsup Q₂ Q₁ Qa)))

/-- Vertical pasting under preconditions: from `Refines P₁ γ₁ eps₁ b a Q₁` and
    `Refines P₂ γ₂ eps₂ c b Q₂`, `c` refines `a` along the composite under the precondition
    `P₂ ⊓ γ₂.pred P₁`, when `γ₂` preserves suprema and binary meets. -/
theorem Refines.vcomp [Heyting BPred] [Heyting CPred] {P₁ : BPred} {P₂ : CPred}
    (hsup : γ₂.SupPreserving.{_, v}) (hmeet : γ₂.MeetPreserving)
    (h₁ : Refines P₁ γ₁ eps₁ b a Q₁) (h₂ : Refines P₂ γ₂ eps₂ c b Q₂) :
    Refines (meet P₂ (γ₂.pred P₁)) (γ₂.comp γ₁) (fun e => eps₂ (eps₁ e)) c a
      (γ₂.relComp Q₂ Q₁) := by
  apply wrp_intro
  intro Qa Ea
  have k₁ := wrp_transport h₁ Qa Ea
  have k₂ := wrp_transport h₂ (γ₁.post Q₁ Qa) (eps₁ Ea)
  refine PartialOrder.rel_trans ?_ (PartialOrder.rel_trans k₂
    (WP.wp_consequence _ _ _ _ (Concretization.post_comp_le hsup Q₂ Q₁ Qa)))
  apply le_meet
  · exact meet_le_of_left_le (meet_le_left _ _)
  · exact PartialOrder.rel_trans (meet_mono_left (meet_le_right _ _))
      (PartialOrder.rel_trans (hmeet _ _) (γ₂.pred_mono k₁))

end Vertical

section Horizontal

variable {mc ma : Type v → Type u} [Monad mc] [Monad ma] {CPred APred : Type w}
  {CE AE : Type w'} [Assertion CPred] [Assertion APred] [Assertion CE] [Assertion AE]
  [WPMonad mc CPred CE] [WPMonad ma APred AE]

/-- Horizontal pasting along `bind`: if `c` refines `a` with return relation `R` and, for all
    `R`-related values, `k cv` refines `g av` under the precondition `R cv av`, then `c >>= k`
    refines `a >>= g`, when the `wp` of `a >>= g` is below the composite `wp` of `a` and `g`
    (the converse of `WPMonad.bind_le_wp_bind` on the abstract side). -/
theorem Refines.bind [Heyting CPred] {γ : Concretization CPred APred} {eps : AE → CE}
    {α β α' β' : Type v} {P : CPred} {c : mc α} {k : α → mc β} {a : ma α'} {g : α' → ma β'}
    {R : α → α' → CPred} {Q : β → β' → CPred}
    (hbind : ∀ (Qa : β' → APred) (Ea : AE),
      wp (a >>= g) Qa Ea ⊑ wp a (fun v => wp (g v) Qa Ea) Ea)
    (hc : Refines P γ eps c a R) (hk : ∀ cv av, Refines (R cv av) γ eps (k cv) (g av) Q) :
    Refines P γ eps (c >>= k) (a >>= g) Q := by
  apply wrp_intro
  intro Qa Ea
  refine PartialOrder.rel_trans (meet_mono_right (γ.pred_mono (hbind Qa Ea))) ?_
  refine PartialOrder.rel_trans (wrp_transport hc _ Ea) ?_
  refine PartialOrder.rel_trans ?_ (WPMonad.bind_le_wp_bind c k _ _)
  apply WP.wp_consequence
  intro cv
  apply iSup_le
  intro av
  exact wrp_transport (hk cv av) Qa Ea

end Horizontal

end RefinementWP
