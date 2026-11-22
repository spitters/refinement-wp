/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.Compose

/-!
# The separating refinement weakest precondition `swrp`

`swrp γ eps c a Q` is the assertion
`⨅ Qa Ea, γ (a Qa Ea) -∗ wp c (fun v => ⨆ w, Q v w ∗ γ (Qa w)) (eps Ea)`.
It is the formula of `wrp` with the separating conjunction `∗` in place of the meet and the
magic wand `-∗` in place of the Heyting implication. The concrete program `c` has a weakest
precondition in `Std.WP` whose assertions have a separating conjunction (`SepAssertion`). The
abstract side is a predicate transformer `a : (AVal → A) → AE → A` on any types of abstract
assertions and exception postconditions, and the concretization is a map `γ : A → Ω`. No rule
needs an order on `A` or `AE`, or monotonicity of `a`.

Where `∗` is the meet, `swrp` at the concretization `γ.pred` and the transformer `wp a` is
`wrp γ eps c a` (`swrp_eq_wrp`).

The frame closure `fwp c Q E := ⨅ F, F -∗ wp c (fun a => Q a ∗ F) E` quantifies the frame inside
the weakest precondition, as in the frame-quantified judgement of Yang and O'Hearn in the form of a
weakest precondition given by Charguéraud. At the frame closure every program frames every
resource, so the frame rule of `swrp` holds with no hypothesis on the program
(`swrp_frame_fwp`). The toolchain has the same construction over upper adjoints,
`Lean.Order.PredTrans.frameClosure` and `Std.WP.WP.withFrameClosure`, whose laws need equational
action laws for the frames and, for sequencing, a unit. The laws of `fwp` need only the inequalities
of `SepAssertion` and no unit; a unit is needed only for `fwp_le_wp`. At separation from a frame,
with exception postconditions not framed, the two closures are equal (`fwp_eq_frameClosure`), so
`framedWP` frames every resource in the sense of `Std.WP.WP.Frames` (`framedWP_frames`).

## Main definitions

* `SepAssertion`: a separating conjunction and a wand on an `Assertion` lattice, with
  monotonicity, symmetry, associativity and the adjunction.
* `SepAssertion.ofHeyting`: the meet and the Heyting implication of a Heyting assertion lattice.
* `swrp`, with its postcondition `swrpPost`; `swrpRelComp`, the composite return relation.
* `fwp`: the frame closure of a weakest precondition; `framedWP` and `framedWPMonad`, the frame
  closure as a `WP` interpretation and as a `WPMonad`.
* `SepAssertionUnit`: a separating conjunction with a unit; `SepAssertionUnit.ofHeyting`, the
  meet with the top element.
* `sepFrame`: separation from a frame, an operator that preserves suprema
  (`sepFrame_preservesSup`).

## Main results

* `swrp_intro`, `swrp_transport`: the adjunction.
* `swrp_mono`, `swrp_mono_abstract`: consequence.
* `swrp_pure`, `swrp_bind`, `swrp_bind_rule`: return and sequencing.
* `swrp_frame`, `swrp_frame_conc`: a resource that the concrete weakest precondition frames is
  framed into the return relation or into the concretization.
* `swrp_vcomp`: vertical pasting. The outer concretization is monotone, preserves suprema over
  the abstract return values, is lax monoidal at the inner precondition and oplax monoidal at
  the inner return relation.
* `swrp_eq_wrp`, `swrp_ofHeyting_eq_wrp`: where `∗` is the meet, `swrp` is `wrp`.
* `le_fwp_iff`, `fwp_monotone`, `fwp_frame`, `le_fwp_pure`, `fwp_bind_le`: the frame closure is
  monotone, frames every resource, and satisfies the lax return and bind laws.
* `le_fwp_of_frames`: a transformer below the weakest precondition that frames every resource is
  below the frame closure.
* `fwp_le_wp`: under a unit, the frame closure entails the weakest precondition.
* `swrp_frame_fwp`: the frame rule of `swrp` at the frame closure.
* `fwp_eq_frameClosure`, `framedWP_frames`: `fwp` is the toolchain's frame closure at `sepFrame`,
  and `framedWP` frames every resource under every guard.

## References

* S. Graf, distillery, for `wrp`.
* D. Frumin, R. Krebbers, L. Birkedal, *ReLoC: A Mechanised Relational Logic for Fine-Grained
  Concurrency*, LICS 2018, for refinement as a wand into a weakest precondition.
* H. Yang, P. W. O'Hearn, *A Semantic Basis for Local Reasoning*, FoSSaCS 2002, for the
  frame-quantified judgement.
* A. Charguéraud, *Separation Logic for Sequential Programs*, ICFP 2020, for the weakest
  precondition with the frame quantified inside.

## Search words

separation logic, separating conjunction, magic wand, residual, refinement weakest precondition,
frame rule, vertical pasting, lax monoidal, oplax monoidal, frame closure, framed weakest
precondition, separating unit
-/

@[expose] public section

set_option autoImplicit false

namespace RefinementWP

open Std.WP Lean.Order
open Lean.Order.PartialOrder (rel_refl rel_trans rel_antisymm rel_of_eq)

universe u u' v v' v'' w w' w'' z z' z''

/-! ## Assertions with a separating conjunction -/

/-- A separating conjunction and a magic wand on an assertion lattice: the conjunction is
monotone, symmetric and associative, and the wand is its right adjoint. -/
class SepAssertion (Ω : Type w) [Assertion Ω] where
  /-- The separating conjunction. -/
  sep : Ω → Ω → Ω
  /-- The magic wand. -/
  wand : Ω → Ω → Ω
  /-- The separating conjunction is monotone. -/
  sep_mono : ∀ {p p' q q' : Ω}, p ⊑ p' → q ⊑ q' → sep p q ⊑ sep p' q'
  /-- The separating conjunction is symmetric. -/
  sep_symm : ∀ {p q : Ω}, sep p q ⊑ sep q p
  /-- The separating conjunction is associative. The converse follows by symmetry. -/
  sep_assoc_le : ∀ {p q r : Ω}, sep (sep p q) r ⊑ sep p (sep q r)
  /-- The wand is right adjoint to the separating conjunction. -/
  le_wand_iff : ∀ {p q r : Ω}, p ⊑ wand q r ↔ sep p q ⊑ r

namespace SepAssertion

variable {Ω : Type w} [Assertion Ω] [SepAssertion Ω] {p p' q q' r : Ω}

/-- The separating conjunction is monotone in its left argument. -/
theorem sep_mono_left (h : p ⊑ p') : sep p q ⊑ sep p' q :=
  sep_mono h rel_refl

/-- The separating conjunction is monotone in its right argument. -/
theorem sep_mono_right (h : q ⊑ q') : sep p q ⊑ sep p q' :=
  sep_mono rel_refl h

/-- The converse direction of associativity. -/
theorem le_sep_assoc : sep p (sep q r) ⊑ sep (sep p q) r :=
  rel_trans sep_symm <| rel_trans sep_assoc_le <| rel_trans sep_symm <|
    rel_trans sep_assoc_le sep_symm

/-- The two right arguments of a nested separating conjunction commute. -/
theorem sep_right_comm : sep (sep p q) r ⊑ sep (sep p r) q :=
  rel_trans sep_assoc_le <| rel_trans (sep_mono_right sep_symm) le_sep_assoc

/-- The separating conjunction preserves suprema in its left argument. -/
theorem iSup_sep_le {ι : Sort u} (f : ι → Ω) :
    sep (iSup f) q ⊑ iSup fun i => sep (f i) q :=
  le_wand_iff.1 <| iSup_le _ _ fun i => le_wand_iff.2 (le_iSup (fun i => sep (f i) q) i)

/-- The separating conjunction preserves suprema in its right argument. -/
theorem sep_iSup_le {ι : Sort u} (f : ι → Ω) :
    sep p (iSup f) ⊑ iSup fun i => sep p (f i) :=
  rel_trans sep_symm <| rel_trans (iSup_sep_le f) <|
    iSup_le _ _ fun i => rel_trans sep_symm (le_iSup (fun i => sep p (f i)) i)

/-- Where the separating conjunction is the meet, the wand is the Heyting implication. -/
theorem wand_eq_himp (hsep : ∀ p q : Ω, sep p q = meet p q) (q r : Ω) :
    wand q r = himp q r := by
  apply rel_antisymm
  · apply le_himp_of_meet_le_left
    rw [meet_comm, ← hsep]
    exact le_wand_iff.1 rel_refl
  · apply (PreservesSup.upperAdjoint_spec (meet q) r _).2
    grind [le_wand_iff, meet_comm]

/-- The meet and the Heyting implication of a Heyting assertion lattice. It is not a global
instance, since an assertion lattice can have another separating conjunction. -/
@[instance_reducible] noncomputable def ofHeyting (Ω : Type w) [Assertion Ω] [Heyting Ω] :
    SepAssertion Ω where
  sep := meet
  wand := himp
  sep_mono := meet_mono
  sep_symm := meet_le_comm
  sep_assoc_le := rel_of_eq meet_assoc
  le_wand_iff := ⟨meet_le_of_le_himp, le_himp⟩

end SepAssertion

open SepAssertion

/-! ## Definition -/

section Generic

variable {CProg : Type u} {CVal : Type v} {AVal : Type v'} {Ω : Type w} {A : Type w'}
  {CE : Type z} {AE : Type z'}
  [Assertion Ω] [SepAssertion Ω] [Assertion CE] [WP CProg CVal Ω CE]

/-- The concrete postcondition of the return relation `Q` and the abstract postcondition `Qa`:
at `v` it is the supremum over `w` of `Q v w` separated from `γ (Qa w)`. -/
noncomputable def swrpPost (γ : A → Ω) (Q : CVal → AVal → Ω) (Qa : AVal → A) : CVal → Ω :=
  fun v => iSup fun w => sep (Q v w) (γ (Qa w))

/-- The separating refinement weakest precondition: the resource that turns each weakest
precondition of the abstract transformer `a`, seen through `γ`, into a weakest precondition of
the concrete program `c`, with exception postconditions mapped by `eps`. -/
noncomputable def swrp (γ : A → Ω) (eps : AE → CE) (c : CProg) (a : (AVal → A) → AE → A)
    (Q : CVal → AVal → Ω) : Ω :=
  iInf fun Qa : AVal → A => iInf fun Ea : AE =>
    wand (γ (a Qa Ea)) (wp c (swrpPost γ Q Qa) (eps Ea))

variable {γ : A → Ω} {eps eps' : AE → CE} {c : CProg} {a a' : (AVal → A) → AE → A}
  {Q Q' : CVal → AVal → Ω} {P : Ω}

/-! ## The adjunction -/

/-- Introduction: `P` entails `swrp` when `P` separated from each concretized abstract
precondition entails the concrete precondition. -/
theorem swrp_intro
    (h : ∀ Qa Ea, sep P (γ (a Qa Ea)) ⊑ wp c (swrpPost γ Q Qa) (eps Ea)) :
    P ⊑ swrp γ eps c a Q :=
  le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => le_wand_iff.2 (h Qa Ea)

/-- Transport: under `P ⊑ swrp`, each concretized abstract precondition separated from `P`
entails the concrete precondition. -/
theorem swrp_transport (h : P ⊑ swrp γ eps c a Q) (Qa : AVal → A) (Ea : AE) :
    sep P (γ (a Qa Ea)) ⊑ wp c (swrpPost γ Q Qa) (eps Ea) :=
  le_wand_iff.1 (rel_trans h (rel_trans (iInf_le _ Qa) (iInf_le _ Ea)))

/-- Transport to a triple of the concrete program. -/
theorem swrp_transport_triple (h : P ⊑ swrp γ eps c a Q) {P' : Ω} {Qa : AVal → A} {Ea : AE}
    (hpre : P' ⊑ γ (a Qa Ea)) : Triple c (sep P P') (swrpPost γ Q Qa) (eps Ea) :=
  ⟨rel_trans (sep_mono_right hpre) (swrp_transport h Qa Ea)⟩

/-! ## Consequence -/

/-- Consequence in the return relation. -/
theorem swrp_mono (hQ : ∀ v w, Q v w ⊑ Q' v w) :
    swrp γ eps c a Q ⊑ swrp γ eps c a Q' :=
  swrp_intro fun Qa Ea => rel_trans (swrp_transport rel_refl Qa Ea) <|
    WP.wp_monotone_post fun v => iSup_le _ _ fun w =>
      rel_trans (sep_mono_left (hQ v w)) (le_iSup (fun w => sep (Q' v w) (γ (Qa w))) w)

/-- Consequence in the abstract transformer, seen through `γ`. -/
theorem swrp_mono_abstract (ha : ∀ Qa Ea, γ (a' Qa Ea) ⊑ γ (a Qa Ea)) :
    swrp γ eps c a Q ⊑ swrp γ eps c a' Q :=
  swrp_intro fun Qa Ea =>
    rel_trans (sep_mono_right (ha Qa Ea)) (swrp_transport rel_refl Qa Ea)

/-! ## Frame -/

/-- Frame: a resource separated from a refinement is separated from its return relation, when
the weakest precondition of `c` frames it and takes the exception map `eps` to `eps'`. -/
theorem swrp_frame {F : Ω}
    (hF : ∀ R Ea, sep (wp c R (eps Ea)) F ⊑ wp c (fun v => sep (R v) F) (eps' Ea)) :
    sep (swrp γ eps c a Q) F ⊑ swrp γ eps' c a (fun v w => sep (Q v w) F) :=
  swrp_intro fun Qa Ea => rel_trans sep_right_comm <|
    rel_trans (sep_mono_left (swrp_transport rel_refl Qa Ea)) <| rel_trans (hF _ Ea) <|
      WP.wp_monotone_post fun v => rel_trans (iSup_sep_le _) <| iSup_le _ _ fun w =>
        rel_trans sep_right_comm (le_iSup (fun w => sep (sep (Q v w) F) (γ (Qa w))) w)

/-- Frame in the concretization: a refinement along `γ` is one along `γ` separated from a
resource that the weakest precondition of `c` frames. -/
theorem swrp_frame_conc {F : Ω}
    (hF : ∀ R Ea, sep (wp c R (eps Ea)) F ⊑ wp c (fun v => sep (R v) F) (eps' Ea)) :
    swrp γ eps c a Q ⊑ swrp (fun x => sep (γ x) F) eps' c a Q :=
  swrp_intro fun Qa Ea => rel_trans le_sep_assoc <|
    rel_trans (sep_mono_left (swrp_transport rel_refl Qa Ea)) <| rel_trans (hF _ Ea) <|
      WP.wp_monotone_post fun v => rel_trans (iSup_sep_le _) <| iSup_le _ _ fun w =>
        rel_trans sep_assoc_le (le_iSup (fun w => sep (Q v w) (sep (γ (Qa w)) F)) w)

end Generic

/-! ## Return and sequencing -/

section Monadic

variable {m : Type v → Type u} [Monad m] {Ω : Type w} {A : Type w'} {CE : Type z} {AE : Type z'}
  [Assertion Ω] [SepAssertion Ω] [Assertion CE] [WPMonad m Ω CE]
  {α α' : Type v} {β : Type v'} {β' : Type v''}
  {γ : A → Ω} {eps : AE → CE}

/-- The return of related values refines the return. -/
theorem swrp_pure {Q : α → β → Ω} (v : α) (w : β) :
    Q v w ⊑ swrp γ eps (pure v : m α) (fun Qa _ => Qa w) Q :=
  swrp_intro fun Qa Ea =>
    rel_trans (le_iSup (fun w => sep (Q v w) (γ (Qa w))) w)
      (WPMonad.pure_le_wp_pure v (swrpPost γ Q Qa) (eps Ea))

variable {c : m α} {f : α → m α'} {a : (β → A) → AE → A} {g : β → (β' → A) → AE → A}
  {ab : (β' → A) → AE → A} {R : α' → β' → Ω}

/-- Sequencing: a refinement whose return relation is the refinement of the continuations
refines the sequence, when the abstract sequence `ab` is below the composite of `a` and `g`
seen through `γ`. -/
theorem swrp_bind (hab : ∀ Qb Ea, γ (ab Qb Ea) ⊑ γ (a (fun w => g w Qb Ea) Ea)) :
    swrp γ eps c a (fun v w => swrp γ eps (f v) (g w) R) ⊑ swrp γ eps (c >>= f) ab R :=
  swrp_intro fun Qb Ea => rel_trans (sep_mono_right (hab Qb Ea)) <|
    rel_trans (swrp_transport rel_refl _ Ea) <|
      rel_trans (WP.wp_monotone_post fun _ => iSup_le _ _ fun _ =>
          swrp_transport rel_refl Qb Ea)
        (WPMonad.bind_le_wp_bind c f _ _)

/-- Sequencing with an intermediate return relation. -/
theorem swrp_bind_rule {P : Ω} {Q : α → β → Ω}
    (hab : ∀ Qb Ea, γ (ab Qb Ea) ⊑ γ (a (fun w => g w Qb Ea) Ea))
    (hc : P ⊑ swrp γ eps c a Q) (hf : ∀ v w, Q v w ⊑ swrp γ eps (f v) (g w) R) :
    P ⊑ swrp γ eps (c >>= f) ab R :=
  rel_trans hc (rel_trans (swrp_mono hf) (swrp_bind hab))

end Monadic

/-! ## Vertical pasting -/

section Pasting

variable {CProg : Type u} {BProg : Type u'} {CVal : Type v} {BVal : Type v'} {AVal : Type v''}
  {Ω : Type w} {B : Type w'} {A : Type w''} {CE : Type z} {BE : Type z'} {AE : Type z''}
  [Assertion Ω] [SepAssertion Ω]

/-- The composite return relation through the outer concretization `γ₂`: at `v x` it is the
supremum over `w` of `Q₂ v w` separated from `γ₂ (Q₁ w x)`. -/
noncomputable def swrpRelComp (γ₂ : B → Ω) (Q₂ : CVal → BVal → Ω) (Q₁ : BVal → AVal → B) :
    CVal → AVal → Ω :=
  fun v x => iSup fun w => sep (Q₂ v w) (γ₂ (Q₁ w x))

variable [Assertion B] [SepAssertion B] [Assertion CE] [Assertion BE]
  [WP CProg CVal Ω CE] [WP BProg BVal B BE]

/-- Vertical pasting. The outer concretization is monotone, preserves the suprema over the
abstract return values, is lax monoidal at the inner precondition and oplax monoidal at the
inner return relation. -/
theorem swrp_vcomp {γ₂ : B → Ω} {γ₁ : A → B} {eps₂ : BE → CE} {eps₁ : AE → BE}
    {c : CProg} {b : BProg} {a : (AVal → A) → AE → A} {P₂ : Ω} {P₁ : B}
    {Q₂ : CVal → BVal → Ω} {Q₁ : BVal → AVal → B}
    (hmono : ∀ {p q : B}, p ⊑ q → γ₂ p ⊑ γ₂ q)
    (hsup : ∀ f : AVal → B, γ₂ (iSup f) ⊑ iSup fun x => γ₂ (f x))
    (hlax : ∀ y, sep (γ₂ P₁) (γ₂ (γ₁ y)) ⊑ γ₂ (sep P₁ (γ₁ y)))
    (hoplax : ∀ w x y, γ₂ (sep (Q₁ w x) (γ₁ y)) ⊑ sep (γ₂ (Q₁ w x)) (γ₂ (γ₁ y)))
    (h₁ : P₁ ⊑ swrp γ₁ eps₁ b a Q₁) (h₂ : P₂ ⊑ swrp γ₂ eps₂ c (wp b) Q₂) :
    sep P₂ (γ₂ P₁) ⊑
      swrp (fun y => γ₂ (γ₁ y)) (fun e => eps₂ (eps₁ e)) c a (swrpRelComp γ₂ Q₂ Q₁) := by
  apply swrp_intro
  intro Qa Ea
  -- The inner precondition moves inside `γ₂`, where the inner refinement applies.
  refine rel_trans sep_assoc_le <|
    rel_trans (sep_mono_right (rel_trans (hlax _) (hmono (swrp_transport h₁ Qa Ea)))) ?_
  refine rel_trans (swrp_transport h₂ _ _) (WP.wp_monotone_post fun v => ?_)
  -- The inner return relation moves out of `γ₂`.
  refine iSup_le _ _ fun w => ?_
  refine rel_trans (sep_mono_right (hsup _)) <| rel_trans (sep_iSup_le _) ?_
  refine iSup_le _ _ fun x => ?_
  refine rel_trans (sep_mono_right (hoplax w x (Qa x))) <| rel_trans le_sep_assoc ?_
  exact rel_trans (sep_mono_left (le_iSup (fun w => sep (Q₂ v w) (γ₂ (Q₁ w x))) w))
    (le_iSup (fun x => sep (swrpRelComp γ₂ Q₂ Q₁ v x) (γ₂ (γ₁ (Qa x)))) x)

end Pasting

/-! ## The separating conjunction as the meet -/

section Meet

variable {CProg AProg : Type u} {CVal AVal : Type v} {CPred APred : Type w} {CE AE : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CE] [Assertion AE]
  [WP CProg CVal CPred CE] [WP AProg AVal APred AE]

/-- **Where the separating conjunction is the meet, `swrp` is `wrp`**: at the concretization
`γ.pred` and the transformer `wp a`. -/
theorem swrp_eq_wrp [SepAssertion CPred] (hsep : ∀ p q : CPred, sep p q = meet p q)
    (γ : Concretization CPred APred) (eps : AE → CE) (c : CProg) (a : AProg)
    (Q : CVal → AVal → CPred) :
    swrp γ.pred eps c (wp a) Q = wrp γ eps c a Q := by
  simp only [swrp, wrp, wand_eq_himp hsep]
  unfold swrpPost Concretization.post
  simp only [hsep]

attribute [local instance] SepAssertion.ofHeyting

/-- At the meet of a Heyting assertion lattice, `swrp` is `wrp`. -/
theorem swrp_ofHeyting_eq_wrp [Heyting CPred] (γ : Concretization CPred APred)
    (eps : AE → CE) (c : CProg) (a : AProg) (Q : CVal → AVal → CPred) :
    swrp γ.pred eps c (wp a) Q = wrp γ eps c a Q :=
  swrp_eq_wrp (fun _ _ => rfl) γ eps c a Q

/-- A functional state relation satisfies the four hypotheses of `swrp_vcomp`. -/
example {σ τ ρ α β δ : Type} {SR : σ → τ → Prop}
    (hfun : ∀ s t t', SR s t → SR s t' → t = t') {γ₁ : (ρ → Prop) → τ → Prop}
    {c : MonoPT σ α} {b : MonoPT τ β} {a : (δ → ρ → Prop) → Unit → ρ → Prop}
    {P₂ : σ → Prop} {P₁ : τ → Prop} {Q₂ : α → β → σ → Prop} {Q₁ : β → δ → τ → Prop}
    (h₁ : P₁ ⊑ swrp γ₁ id b a Q₁)
    (h₂ : P₂ ⊑ swrp (Concretization.ofStateRel SR).pred id c (wp b) Q₂) :
    meet P₂ ((Concretization.ofStateRel SR).pred P₁) ⊑
      swrp (fun y => (Concretization.ofStateRel SR).pred (γ₁ y)) id c a
        (swrpRelComp (Concretization.ofStateRel SR).pred Q₂ Q₁) :=
  swrp_vcomp (Concretization.ofStateRel SR).pred_mono
    (Concretization.ofStateRel_supPreserving SR)
    (fun _ => Concretization.ofStateRel_meetPreserving SR hfun _ _)
    (fun _ _ _ => le_meet _ _ _
      ((Concretization.ofStateRel SR).pred_mono (meet_le_left _ _))
      ((Concretization.ofStateRel SR).pred_mono (meet_le_right _ _)))
    h₁ h₂

/-- A program that leaves the state unchanged satisfies the hypothesis of the frame rules. -/
example {σ A α β : Type} {γ : A → σ → Prop} {a : (β → A) → Unit → A}
    {Q : α → β → σ → Prop} (f : σ → α) (F : σ → Prop) :
    meet (swrp γ id (optD fun s => some (f s, s)) a Q) F ⊑
      swrp γ id (optD fun s => some (f s, s)) a (fun v w => meet (Q v w) F) :=
  swrp_frame (F := F) fun R Ea s h => by
    simp only [SepAssertion.sep, meet_apply, meet_prop_eq_and, wp_optD_apply] at h ⊢
    exact h

end Meet

/-! ## The frame closure of a weakest precondition -/

section FrameClosure

variable {CProg : Type u} {CVal : Type v} {Ω : Type w} {CE : Type z}
  [Assertion Ω] [SepAssertion Ω] [Assertion CE] [WP CProg CVal Ω CE]

/-- The frame closure of the weakest precondition: the meet over all frames `F` of the wand from
`F` into the weakest precondition of the postcondition separated from `F`. -/
noncomputable def fwp (c : CProg) (Q : CVal → Ω) (E : CE) : Ω :=
  iInf fun F : Ω => wand F (wp c (fun a => sep (Q a) F) E)

variable {c : CProg} {Q Q' : CVal → Ω} {E E' : CE} {P : Ω}

/-- An assertion entails the frame closure when, separated from each frame, it entails the weakest
precondition of the postcondition separated from that frame. -/
theorem le_fwp_iff : P ⊑ fwp c Q E ↔ ∀ F, sep P F ⊑ wp c (fun a => sep (Q a) F) E :=
  ⟨fun h F => le_wand_iff.1 (rel_trans h (iInf_le _ F)),
    fun h => le_iInf _ _ fun F => le_wand_iff.2 (h F)⟩

/-- The frame closure separated from a frame entails the weakest precondition at that frame. -/
theorem sep_fwp_le (F : Ω) : sep (fwp c Q E) F ⊑ wp c (fun a => sep (Q a) F) E :=
  le_fwp_iff.1 rel_refl F

/-- The frame closure is monotone in the normal and the exception postcondition. -/
theorem fwp_monotone (hQ : ∀ a, Q a ⊑ Q' a) (hE : E ⊑ E') : fwp c Q E ⊑ fwp c Q' E' :=
  le_fwp_iff.2 fun F => rel_trans (sep_fwp_le F) <|
    WP.wp_monotone (fun a => sep_mono_left (hQ a)) hE

/-- The frame closure is monotone in the normal postcondition. -/
theorem fwp_mono (hQ : ∀ a, Q a ⊑ Q' a) : fwp c Q E ⊑ fwp c Q' E :=
  fwp_monotone hQ rel_refl

/-- Frame: at the frame closure every program frames every resource. -/
theorem fwp_frame (R : Ω) : sep (fwp c Q E) R ⊑ fwp c (fun a => sep (Q a) R) E :=
  le_fwp_iff.2 fun _ => rel_trans sep_assoc_le <| rel_trans (sep_fwp_le _) <|
    WP.wp_monotone_post fun _ => le_sep_assoc

/-- Universal property: a transformer of the postconditions of `c` that is below the weakest
precondition of `c` and frames every resource is below the frame closure. -/
theorem le_fwp_of_frames (w : (CVal → Ω) → CE → Ω) (hle : ∀ Q, w Q E ⊑ wp c Q E)
    (hframe : ∀ Q F, sep (w Q E) F ⊑ w (fun a => sep (Q a) F) E) :
    w Q E ⊑ fwp c Q E :=
  le_fwp_iff.2 fun F => rel_trans (hframe Q F) (hle _)

/-- The frame closure as a weakest precondition interpretation of `CProg`. It is a definition and
not an instance, since `CProg` has its own interpretation. -/
@[instance_reducible] noncomputable def framedWP : WP CProg CVal Ω CE where
  trans c := ⟨fwp c⟩
  trans_monotone _ _ _ _ _ hE hQ := fwp_monotone hQ hE

/-- Unfolding `framedWP`: its weakest precondition is the frame closure. -/
theorem framedWP_wp (c : CProg) (Q : CVal → Ω) (E : CE) :
    (framedWP : WP CProg CVal Ω CE).wp c Q E = fwp c Q E :=
  rfl

/-- Frame for `swrp` at the framed weakest precondition: a resource separated from a refinement is
separated from its return relation, with no hypothesis on the program. -/
theorem swrp_frame_fwp {AVal : Type v'} {A : Type w'} {AE : Type z'} {γ : A → Ω} {eps : AE → CE}
    {a : (AVal → A) → AE → A} {Qr : CVal → AVal → Ω} (F : Ω) :
    sep (@swrp CProg CVal AVal Ω A CE AE _ _ _ framedWP γ eps c a Qr) F ⊑
      @swrp CProg CVal AVal Ω A CE AE _ _ _ framedWP γ eps c a (fun v w => sep (Qr v w) F) :=
  @swrp_frame CProg CVal AVal Ω A CE AE _ _ _ framedWP γ eps eps c a Qr F
    fun _ _ => fwp_frame F

end FrameClosure

section FrameClosureMonadic

variable {m : Type v → Type u} [Monad m] {Ω : Type w} {CE : Type z}
  [Assertion Ω] [SepAssertion Ω] [Assertion CE] [WPMonad m Ω CE] {α β : Type v}

/-- Return: the postcondition at `x` entails the frame closure of `pure x`. -/
theorem le_fwp_pure (x : α) (Q : α → Ω) (E : CE) : Q x ⊑ fwp (pure x : m α) Q E :=
  le_fwp_iff.2 fun F => WPMonad.pure_le_wp_pure x (fun a => sep (Q a) F) E

/-- Lax bind: the frame closure of `c` at the frame closures of the continuations entails the
frame closure of the sequence. -/
theorem fwp_bind_le (c : m α) (f : α → m β) (Q : β → Ω) (E : CE) :
    fwp c (fun a => fwp (f a) Q E) E ⊑ fwp (c >>= f) Q E :=
  le_fwp_iff.2 fun F => rel_trans (sep_fwp_le F) <|
    rel_trans (WP.wp_monotone_post fun _ => sep_fwp_le F) (WPMonad.bind_le_wp_bind c f _ E)

/-- The frame closure as a weakest precondition monad. It is a definition and not an instance,
since `m` has its own interpretation. -/
@[instance_reducible] noncomputable def framedWPMonad : WPMonad m Ω CE where
  toLawfulMonad := inferInstance
  toWP _ := framedWP
  pure_le_wp_pure x Q E := le_fwp_pure x Q E
  bind_le_wp_bind c f Q E := fwp_bind_le c f Q E

end FrameClosureMonadic

/-! ## A unit for the separating conjunction -/

/-- A separating conjunction with a unit `emp`. -/
class SepAssertionUnit (Ω : Type w) [Assertion Ω] extends SepAssertion Ω where
  /-- The unit of the separating conjunction. -/
  emp : Ω
  /-- Separating with the unit weakens. -/
  sep_emp_le : ∀ {p : Ω}, sep p emp ⊑ p
  /-- Separating with the unit strengthens. -/
  le_sep_emp : ∀ {p : Ω}, p ⊑ sep p emp

/-- The meet and the Heyting implication of a Heyting assertion lattice, with the top element as
unit. -/
@[instance_reducible] noncomputable def SepAssertionUnit.ofHeyting (Ω : Type w) [Assertion Ω]
    [Heyting Ω] : SepAssertionUnit Ω where
  toSepAssertion := SepAssertion.ofHeyting Ω
  emp := ⊤
  sep_emp_le := meet_le_left _ _
  le_sep_emp := le_meet _ _ _ rel_refl (le_top _)

open SepAssertionUnit in
/-- Soundness: under a unit, the frame closure entails the weakest precondition. -/
theorem fwp_le_wp {CProg : Type u} {CVal : Type v} {Ω : Type w} {CE : Type z}
    [Assertion Ω] [SepAssertionUnit Ω] [Assertion CE] [WP CProg CVal Ω CE]
    (c : CProg) (Q : CVal → Ω) (E : CE) : fwp c Q E ⊑ wp c Q E :=
  rel_trans le_sep_emp <| rel_trans (sep_fwp_le emp) (WP.wp_monotone_post fun _ => sep_emp_le)

/-! ## The frame closure of the toolchain -/

section StdFrame

variable {Ω : Type w} [Assertion Ω] [SepAssertion Ω]

/-- Separation from the frame `F`, as an operator on assertions. -/
def sepFrame (F p : Ω) : Ω := sep p F

/-- Separation from a frame preserves suprema, by the wand adjunction. -/
instance sepFrame_preservesSup (F : Ω) : PreservesSup (sepFrame F) where
  map_sup s := rel_antisymm
    (le_wand_iff.1 <| sup_le _ fun x hx => le_wand_iff.2 (le_sup _ ⟨x, hx, rfl⟩))
    (sup_le _ (by rintro _ ⟨x, hx, rfl⟩; exact sep_mono_left (le_sup _ hx)))

/-- Separation from the frame `sep r' r` is separation from `r'` and then from `r`. -/
theorem sepFrame_comp (r r' p : Ω) : sepFrame (sep r' r) p = sepFrame r (sepFrame r' p) :=
  rel_antisymm le_sep_assoc sep_assoc_le

/-- The wand from `F` is the upper adjoint of separation from `F`. -/
theorem wand_eq_upperAdjoint (F r : Ω) : wand F r = PreservesSup.upperAdjoint (sepFrame F) r :=
  rel_antisymm (PreservesSup.le_upperAdjoint _ (le_wand_iff.1 rel_refl))
    (le_wand_iff.2 (PreservesSup.upperAdjoint_le (sepFrame F) r))

variable {CProg : Type u} {CVal : Type v} {CE : Type z} [Assertion CE] [WP CProg CVal Ω CE]

/-- The frame closure `fwp` is the toolchain's frame closure of the weakest precondition at
separation from a frame, with exception postconditions not framed. -/
theorem fwp_eq_frameClosure (c : CProg) (Q : CVal → Ω) (E : CE) :
    fwp c Q E = ((WP.trans c).frameClosure (opE := FrameOp.ignore) sepFrame).apply Q E := by
  unfold fwp
  exact congrArg iInf (funext fun F => wand_eq_upperAdjoint F _)

/-- At the framed weakest precondition every program frames every resource under every guard, in
the sense of `Std.WP.WP.Frames`. -/
theorem framedWP_frames (x : CProg) (F P : Ω) :
    @WP.Frames CProg CVal Ω CE _ _ framedWP Ω sepFrame FrameOp.ignore _ x F P :=
  @WP.frames_of_frameClosure CProg CVal Ω CE _ _ framedWP Ω sepFrame FrameOp.ignore _
    (fun r r' => sep r' r) sepFrame_comp (fun _ _ _ => rfl) x F P
    ⟨fun x => WP.trans x, fun x => PredTrans.ext fun Q E => fwp_eq_frameClosure x Q E⟩

end StdFrame

open SepAssertionUnit in
/-- Separation from the unit is the identity. -/
theorem sepFrame_emp {Ω : Type w} [Assertion Ω] [SepAssertionUnit Ω] (p : Ω) :
    sepFrame emp p = p :=
  rel_antisymm sep_emp_le le_sep_emp

end RefinementWP
