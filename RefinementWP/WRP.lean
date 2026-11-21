/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.WP

/-!
# The refinement weakest precondition `wrp`

`wrp` is the refinement weakest precondition of S. Graf's distillery, written here from its
published formula, with credit:
`wrp γ c a Q E = ⨅ Qa Ea, γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (ePosts γ E Ea)`
(<https://github.com/sgraf812/distillery/blob/a5cc0e23183f92e37dfbf647a39dd8d8d30df960/Distillery/WRP.lean#L46-L49>),
over the concretizations of
<https://github.com/sgraf812/distillery/blob/a5cc0e23183f92e37dfbf647a39dd8d8d30df960/Distillery/Concretization.lean#L28-L42>.
The program logic is the toolchain's `Std.WP`, and the package depends on nothing else. The
definitions are restricted to a single exception layer: the exception postcondition map
`ePosts γ E` is a function `eps : AE → CE` from abstract to concrete exception postconditions.
They are to be replaced by distillery's when distillery has a licence and a release toolchain.

A refinement `Refines P γ eps c a Q` states that every `wp` fact of the abstract program `a`,
concretized by `γ` and met with `P`, entails the corresponding `wp` fact of the concrete program
`c`, with return values related by `Q`. At `P = ⊤` it is the lax square
`γ ∘ wp a ≤ wp c ∘ γ.post Q` of data refinement by forward simulation.

The abstract programs of the comparison are monotone predicate transformers on state
predicates (`MonoPT`), the standard construction of the refinement calculus; a failure is the
transformer with value `False`, so its weakest precondition is `⊥`.

## Main definitions

* `Concretization`: a monotone map from abstract to concrete assertions; `Concretization.post`,
  the concrete postcondition of a return relation and an abstract postcondition;
  `Concretization.ofStateRel`, the concretization of a state relation.
* `wrp`: the refinement weakest precondition; `Refines P γ eps c a Q`: `P ⊑ wrp γ eps c a Q`.
* `MonoPT`: monotone predicate transformers on state predicates, with their `WP` instance.
* `optD f`: the `MonoPT` program of a partial state transformer `f`.

## Main results

* `wrp_intro`, `wrp_transport`: the introduction and elimination rules of `wrp`.
* `refines_optD_iff`: refinement of `optD f` by a concrete program whose transformer at the
  exception postcondition `⊥` is the angelic transformer of a step relation `T` is the forward
  simulation of `f` by `T`.
-/

@[expose] public section

set_option autoImplicit false

namespace RefinementWP

open Std.WP Lean.Order

universe u v w w'

/-! ## Concretizations -/

/-- A monotone map from abstract assertions to concrete assertions. -/
structure Concretization (CPred APred : Type w) [Assertion CPred] [Assertion APred] where
  /-- The concrete assertion of an abstract assertion. -/
  pred : APred → CPred
  /-- `pred` is monotone. -/
  pred_mono : ∀ {p q : APred}, p ⊑ q → pred p ⊑ pred q

namespace Concretization

variable {CPred APred : Type w} [Assertion CPred] [Assertion APred]

/-- The concrete postcondition of the return relation `Q` and the abstract postcondition `Qa`:
    at `cv` it is the supremum over `av` of `Q cv av` met with the concretization of `Qa av`. -/
noncomputable def post (γ : Concretization CPred APred) {CVal AVal : Type v}
    (Q : CVal → AVal → CPred) (Qa : AVal → APred) : CVal → CPred :=
  fun cv => iSup fun av => meet (Q cv av) (γ.pred (Qa av))

/-- The concrete postcondition over state predicates, pointwise. -/
theorem post_apply {σ : Type} {APred' : Type} [Assertion APred']
    (γ : Concretization (σ → Prop) APred') {CVal AVal : Type}
    (Q : CVal → AVal → σ → Prop) (Qa : AVal → APred') (cv : CVal) (s : σ) :
    γ.post Q Qa cv s ↔ ∃ av, Q cv av s ∧ γ.pred (Qa av) s := by
  simp only [post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and]

/-- The concretization of a state relation `SR`: a concrete state satisfies the image of `P`
    when it is `SR`-related to an abstract state satisfying `P`. -/
def ofStateRel {σ A : Type} (SR : σ → A → Prop) : Concretization (σ → Prop) (A → Prop) where
  pred P s := ∃ a, SR s a ∧ P a
  pred_mono h _ := fun ⟨a, hs, hp⟩ => ⟨a, hs, h a hp⟩

end Concretization

/-! ## The refinement weakest precondition -/

section WRPDef

variable {CProg AProg : Type u} {CVal AVal : Type v} {CPred APred : Type w} {CE AE : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CE] [Assertion AE]
  [WP CProg CVal CPred CE] [WP AProg AVal APred AE]

/-- The refinement weakest precondition: the weakest concrete assertion under which every
    `wp` fact of the abstract program `a` transports through `γ`, the return relation `Q` and
    the exception map `eps` to a `wp` fact of the concrete program `c`. -/
noncomputable def wrp (γ : Concretization CPred APred) (eps : AE → CE) (c : CProg) (a : AProg)
    (Q : CVal → AVal → CPred) : CPred :=
  iInf fun Qa : AVal → APred => iInf fun Ea : AE =>
    himp (γ.pred (wp a Qa Ea)) (wp c (γ.post Q Qa) (eps Ea))

/-- Refinement under the precondition `P`: `P` entails the refinement weakest precondition. -/
def Refines (P : CPred) (γ : Concretization CPred APred) (eps : AE → CE) (c : CProg)
    (a : AProg) (Q : CVal → AVal → CPred) : Prop :=
  P ⊑ wrp γ eps c a Q

variable {γ : Concretization CPred APred} {eps : AE → CE} {P : CPred} {c : CProg} {a : AProg}
  {Q : CVal → AVal → CPred}

/-- Introduction rule of `wrp`: `P` entails `wrp` when, for every abstract postcondition pair,
    `P` met with the concretized abstract precondition entails the concrete precondition. -/
theorem wrp_intro
    (h : ∀ (Qa : AVal → APred) (Ea : AE),
      meet P (γ.pred (wp a Qa Ea)) ⊑ wp c (γ.post Q Qa) (eps Ea)) :
    P ⊑ wrp γ eps c a Q :=
  le_iInf _ _ fun Qa => le_iInf _ _ fun Ea =>
    le_himp (PartialOrder.rel_trans meet_le_comm (h Qa Ea))

/-- Elimination rule of `wrp` (transport): under `P ⊑ wrp …`, each `wp` fact of the abstract
    program, concretized and met with `P`, entails the corresponding concrete `wp` fact. -/
theorem wrp_transport [Heyting CPred] (h : P ⊑ wrp γ eps c a Q)
    (Qa : AVal → APred) (Ea : AE) :
    meet P (γ.pred (wp a Qa Ea)) ⊑ wp c (γ.post Q Qa) (eps Ea) :=
  meet_le_of_le_himp
    (PartialOrder.rel_trans h (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea)))

end WRPDef

/-! ## Abstract programs: monotone predicate transformers -/

/-- A monotone predicate transformer on state predicates over `A` with values in `B`: the
    abstract programs of the refinement calculus. -/
structure MonoPT (A B : Type) where
  /-- The weakest precondition of a postcondition. -/
  trans : (B → A → Prop) → A → Prop
  /-- `trans` is monotone in the postcondition. -/
  mono : ∀ Q Q' : B → A → Prop, (∀ b a, Q b a → Q' b a) → ∀ a, trans Q a → trans Q' a

/-- The weakest precondition of a `MonoPT` is its transformer; the exception postcondition is
    trivial. -/
instance MonoPT.instWP (A B : Type) : WP (MonoPT A B) B (A → Prop) Unit where
  wpTrans x := ⟨fun Q _ => x.trans Q⟩
  wp_trans_monotone x := fun Q Q' _ _ _ hQ => x.mono Q Q' hQ

/-- The `MonoPT` program of a partial state transformer `f`: it establishes `Q` at `a` when
    `f a = some p` and `Q p.1 p.2`, and nothing when `f a = none`. -/
def optD {A B : Type} (f : A → Option (B × A)) : MonoPT A B where
  trans Q a := match f a with
    | some p => Q p.1 p.2
    | none => False
  mono Q Q' h a := by
    split
    · exact h _ _
    · exact id

/-- The weakest precondition of `optD f` (the unfolding lemma of `optD`). -/
theorem wp_optD_apply {A B : Type} (f : A → Option (B × A)) (Q : B → A → Prop) (E : Unit)
    (a : A) :
    wp (optD f) Q E a = match f a with
      | some p => Q p.1 p.2
      | none => False := rfl

/-! ## Refinement of a partial state transformer is forward simulation -/

section ForwardSimulation

variable {σ A B α CProg CE : Type} [Assertion CE] [WP CProg α (σ → Prop) CE]

/-- Refinement of `optD f` by a concrete program `c`, at the concretization of `SR`, the
    return relation `Rv` and the exception map with value `⊥`, is the forward simulation of `f`
    by `T`, when the transformer of `c` at the exception postcondition `⊥` is the angelic
    transformer of the step relation `T`. -/
theorem refines_optD_iff {SR : σ → A → Prop} {Rv : B → α → Prop} {f : A → Option (B × A)}
    {T : σ → α → σ → Prop} (c : CProg)
    (hc : ∀ (Q : α → σ → Prop) (s : σ), wp c Q bot s ↔ ∃ v s', T s v s' ∧ Q v s') :
    Refines top (Concretization.ofStateRel SR) (fun _ : Unit => (bot : CE)) c (optD f)
        (fun v b _ => Rv b v) ↔
      ∀ s a p, SR s a → f a = some p → ∃ v s', T s v s' ∧ Rv p.1 v ∧ SR s' p.2 := by
  constructor
  · intro h s a p hs hf
    have h1 := wrp_transport h (fun b a' => b = p.1 ∧ a' = p.2) () s
    rw [meet_apply, meet_prop_eq_and] at h1
    obtain ⟨v, s', hT, hpost⟩ := (hc _ s).1 (h1 ⟨by simp only [top_apply, top_prop_eq],
      a, hs, by rw [wp_optD_apply, hf]; exact ⟨rfl, rfl⟩⟩)
    obtain ⟨b, hR, a', hs', rfl, rfl⟩ := (Concretization.post_apply ..).1 hpost
    exact ⟨v, s', hT, hR, hs'⟩
  · intro h
    apply wrp_intro
    intro Qa Ea s hs
    grind only [= meet_apply, = top_prop_eq, Concretization.ofStateRel.eq_def, wp_optD_apply,
      Concretization.post_apply]

end ForwardSimulation

end RefinementWP
