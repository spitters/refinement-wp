/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.Compose
public import RefinementWP.Tactic
public import Std.WP

/-!
# A registry of refinements and the structural tactic `wrp_step`

The refinement of a composite follows from the refinements of its parts by `Refines.bind`. This
module registers the refinement of a single function as an instance of `RefinesCall`, and the
tactic `wrp_step` uses the registered refinements, reflexivity along the identity and
sequencing. The goals it does not decide are left, for example to `wrp_vcgen`.

Sequencing needs the converse of `WPMonad.bind_le_wp_bind` on the abstract side, which the
class `WPMonadExact` of `RefinementWP.Exact` states.

A return relation that does not depend on the state, such as equality of the returned values, is
the precondition of the continuations. The class `PurePre` recognizes it, and `wrp_step` turns it
into a hypothesis, so that a refinement registered at related arguments applies.

## Main definitions

* `RefinesCall c a γ eps pre R`: the registered refinement of `a` by `c` under `pre`.
* `PurePre P φ`: the precondition `P` is the proposition `φ`.
* `wrp_step`, `wrp_step using R`, `wrp_steps`: the structural tactic, sequencing at a given
  return relation, and the repetition of the tactic.

## Main results

* `Refines.mono`: refinement is antitone in the precondition and monotone in the return
  relation.
* `Refines.of_pure`: a pure precondition becomes a hypothesis.
* `Refines.of_call`, `Refines.bind_call`: the rules of a registered refinement, alone and as the
  first part of a sequence.
* `Refines.bind_refl`, `Refines.seq`, `Refines.bind_assoc`: the rules of sequencing after an
  identical first part, at a given return relation, and for nested sequences.
* `StepExamples.refines_add_four`: a refinement of a sequence of `optD` steps, proved by
  `wrp_vcgen` alone.
-/

@[expose] public section

set_option autoImplicit false

namespace RefinementWP

open Std.WP Lean.Order

universe u v w w'

/-! ## Pure preconditions -/

/-- The precondition `P` is the proposition `φ`, which instance search computes from `P`. -/
class PurePre {Pred : Type w} [Assertion Pred] (P : Pred) (φ : outParam Prop) : Prop where
  /-- `P` is the embedding of `φ`. -/
  eq_ofProp : P = CompleteLattice.ofProp φ

/-- An embedded proposition is pure. -/
instance PurePre.ofProp {Pred : Type w} [Assertion Pred] (φ : Prop) :
    PurePre (CompleteLattice.ofProp φ : Pred) φ :=
  ⟨rfl⟩

/-- The equality return relation is pure at each pair of values. -/
instance PurePre.eqRel {Pred : Type w} [Assertion Pred] {α : Type v} (x y : α) :
    PurePre (RefinementWP.eqRel (CPred := Pred) x y) (x = y) :=
  ⟨rfl⟩

/-- A proposition as an assertion is pure. -/
instance (priority := low) PurePre.prop (φ : Prop) : PurePre φ φ :=
  ⟨(CompleteLattice.ofProp_prop_eq φ).symm⟩

/-- An assertion that is constant in the state is pure when its value is. -/
instance PurePre.const {σ : Type v} {Pred : Type w} [Assertion Pred] {P : Pred} {φ : Prop}
    [h : PurePre P φ] : PurePre (fun _ : σ => P) φ where
  eq_ofProp := by
    funext s
    rw [h.eq_ofProp]
    by_cases hφ : φ <;> simp [CompleteLattice.ofProp, hφ]

/-! ## The registry -/

section Registry

variable {CProg AProg : Type u} {CVal AVal : Type v} {CPred APred : Type w} {CE AE : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CE] [Assertion AE]
  [WP CProg CVal CPred CE] [WP AProg AVal APred AE]

/-- The registered refinement of the call `a` by the call `c` along `γ` and `eps`. Instance
    search computes the condition `pre` on the arguments of the two calls and the return relation
    `R` from the calls. An instance whose arguments are variables registers a function at all
    arguments. -/
class RefinesCall (c : CProg) (a : AProg) (γ : Concretization CPred APred) (eps : AE → CE)
    (pre : outParam Prop) (R : outParam (CVal → AVal → CPred)) : Prop where
  /-- The refinement, when the arguments satisfy `pre`. -/
  refines : pre → Refines top γ eps c a R

variable [Heyting CPred] {γ : Concretization CPred APred} {eps : AE → CE} {P P' : CPred}
  {c : CProg} {a : AProg} {Q R : CVal → AVal → CPred}

/-- Refinement is monotone in the return relation and antitone in the precondition. -/
theorem Refines.mono (hP : P ⊑ P') (hQ : ∀ cv av, R cv av ⊑ Q cv av)
    (h : Refines P' γ eps c a R) : Refines P γ eps c a Q := by
  apply wrp_intro
  intro Qa Ea
  refine PartialOrder.rel_trans (meet_mono_left hP) ?_
  refine PartialOrder.rel_trans (wrp_transport h Qa Ea) (WP.wp_monotone_post ?_)
  intro cv
  apply iSup_le
  intro av
  exact le_iSup_of_le av (meet_mono_left (hQ cv av))

omit [Heyting CPred] in
/-- A pure precondition becomes a hypothesis of a refinement under `⊤`. -/
theorem Refines.of_pure {φ : Prop} [hP : PurePre P φ] (h : φ → Refines top γ eps c a Q) :
    Refines P γ eps c a Q := by
  unfold Refines
  rw [hP.eq_ofProp]
  exact CompleteLattice.ofProp_le _ _ h

/-- A registered refinement proves the refinement of its calls under every precondition, at
    every weaker return relation, when the arguments satisfy its condition. -/
theorem Refines.of_call {pre : Prop} [h : RefinesCall c a γ eps pre R] (hpre : pre)
    (hQ : ∀ cv av, R cv av ⊑ Q cv av) : Refines P γ eps c a Q :=
  (h.refines hpre).mono (le_top P) hQ

end Registry

/-! ## The rules of sequencing -/

section Sequencing

variable {mc ma : Type v → Type u} [Monad mc] [Monad ma] {CPred APred : Type w} {CE AE : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CE] [Assertion AE]
  [WPMonad mc CPred CE] [WPMonad ma APred AE]
  {γ : Concretization CPred APred} {eps : AE → CE} {α β α' β' : Type v} {P : CPred}
  {c : mc α} {k : α → mc β} {a : ma α'} {g : α' → ma β'} {Q : β → β' → CPred}

/-- Sequencing at the return relation `R`, with the law of `Refines.bind` found by instance
    search. -/
theorem Refines.seq [Heyting CPred] [WPMonadExact ma] (R : α → α' → CPred)
    (hc : Refines P γ eps c a R) (hk : ∀ cv av, Refines (R cv av) γ eps (k cv) (g av) Q) :
    Refines P γ eps (c >>= k) (a >>= g) Q :=
  Refines.bind (WPMonadExact.wp_bind_le a g) hc hk

/-- Sequencing after a registered refinement: its return relation is the precondition of the
    continuations. -/
theorem Refines.bind_call [Heyting CPred] [WPMonadExact ma] {pre : Prop} {R : α → α' → CPred}
    [RefinesCall c a γ eps pre R] (hpre : pre)
    (hk : ∀ cv av, Refines (R cv av) γ eps (k cv) (g av) Q) :
    Refines P γ eps (c >>= k) (a >>= g) Q :=
  Refines.seq R (Refines.of_call hpre fun _ _ => PartialOrder.rel_refl) hk

/-- Sequencing after an identical first part along the identity: the continuations start from
    equal values. -/
theorem Refines.bind_refl [Heyting CPred] [WPMonadExact mc] {g : α → mc β'}
    (hk : ∀ cv av, Refines (eqRel (CPred := CPred) cv av) Concretization.id (fun e : CE => e)
      (k cv) (g av) Q) :
    Refines P Concretization.id (fun e : CE => e) (c >>= k) (c >>= g) Q :=
  Refines.seq _ (Refines.refl P c) hk

/-- Sequences nested to the left refine when the same sequences nested to the right do. -/
theorem Refines.bind_assoc {δ δ' : Type v} {l : β → mc δ} {r : β' → ma δ'} {Q : δ → δ' → CPred}
    (h : Refines P γ eps (c >>= fun x => k x >>= l) (a >>= fun x => g x >>= r) Q) :
    Refines P γ eps ((c >>= k) >>= l) ((a >>= g) >>= r) Q := by
  simpa only [LawfulMonad.bind_assoc] using h

end Sequencing

end RefinementWP

end

/-! ## The tactic -/

public meta section

namespace RefinementWP

open Lean

/--
`wrp_step` makes one structural step at a goal `Refines P γ eps c a Q`, the first that applies:

1. a pure precondition `P` other than `⊤` (an instance of `PurePre`) becomes a hypothesis, which
   is substituted when it equates two variables;
2. a refinement of `c` and `a` registered as an instance of `RefinesCall` proves the goal;
3. reflexivity proves it when `c` and `a` are the same program along the identity;
4. for `c = c₁ >>= k` and `a = a₁ >>= g`, a registered refinement of `c₁` and `a₁`, or
   reflexivity, leaves the refinement of the continuations under its return relation;
5. sequences nested to the left on both sides are nested to the right.

The condition of a registered refinement on the arguments, and the comparison of its return
relation with `Q`, are left as goals when they are not immediate. A registered refinement holds
under `⊤`, so these goals do not mention a precondition `P` on the state. Programs are matched up to
reducible definitions and instances, so a composite definition is unfolded before the tactic is
used.

`wrp_step using R` sequences at the return relation `R` and leaves both parts as goals; it is
the step for a first part that the registry lacks.
-/
syntax (name := wrpStep) "wrp_step" (" using " term)? : tactic

macro_rules
  | `(tactic| wrp_step) =>
    `(tactic| open _root_.Std.WP _root_.Lean.Order in (
      first
        | (fail_if_success (with_reducible_and_instances refine Iff.mpr refines_top_iff ?_))
          with_reducible_and_instances refine Refines.of_pure fun h => ?_
          try subst h
        | (with_reducible_and_instances refine Refines.of_call ?_ ?_) <;>
            first
              | with_reducible assumption
              | with_reducible exact True.intro
              | with_reducible rfl
              | exact fun _ _ => Lean.Order.PartialOrder.rel_refl
              | (intro _ _
                 simp -failIfUnchanged only [Lean.Order.top_apply]
                 exact Lean.Order.le_top _)
              | exact fun _ _ _ _ => True.intro
              | skip
        | with_reducible_and_instances exact Refines.refl _ _
        | (with_reducible_and_instances refine Refines.bind_call ?_ fun cv av => ?_) <;>
            first
              | with_reducible assumption
              | with_reducible exact True.intro
              | with_reducible rfl
              | skip
        | with_reducible_and_instances refine Refines.bind_refl fun cv av => ?_
        | with_reducible_and_instances refine Refines.bind_assoc ?_
        | fail "wrp_step: expected a goal `Refines P γ eps c a Q` of one of four shapes: \
            (1) P is pure and other than ⊤; \
            (2) c and a are registered by `RefinesCall`, or are equal along the identity; \
            (3) c = c₁ >>= k and a = a₁ >>= g, with c₁ and a₁ as in (2) and an exact abstract \
            monad; (4) c and a are both sequences nested to the left. \
            For other c₁ and a₁, `wrp_step using R` gives their return relation"))
  | `(tactic| wrp_step using $R) =>
    `(tactic| open _root_.Std.WP _root_.Lean.Order in (
      first
        | with_reducible_and_instances refine Refines.seq $R ?_ fun cv av => ?_
        | fail "wrp_step using R: expected a goal `Refines P γ eps (c₁ >>= k) (a₁ >>= g) Q` \
            over an exact abstract monad and a Heyting lattice, with R relating the values of \
            c₁ and a₁"))

/--
`wrp_steps` repeats `wrp_step` on the goal and on the goals it leaves, and fails when the first
step fails. The goals left are those at which no step applies.
-/
syntax (name := wrpSteps) "wrp_steps" : tactic

macro_rules
  | `(tactic| wrp_steps) => `(tactic| (wrp_step <;> repeat' wrp_step))

end RefinementWP

end

/-! ## Examples -/

@[expose] public section

namespace RefinementWP.StepExamples

open Std.WP Lean.Order RefinementWP.TacticExamples

/-- The addition of `n` to the first register. -/
def addX (n : Nat) : StateT Regs Option Unit :=
  modify fun s => { s with x := s.x + n }

/-- The value of the first register. -/
def readX : StateT Regs Option Nat := do
  let s ← get
  return s.x

/-- The assignment of `v` to the second register, which has no registered refinement. -/
def setY (v : Nat) : StateT Regs Option Unit :=
  modify fun s => { s with y := v }

/-- The addition of `n` to the first component of a pair. -/
def addFst (n : Nat) : MonoPT (Nat × Nat) Unit :=
  optD fun a => some ((), (a.1 + n, a.2))

/-- The first component of a pair. -/
def readFst : MonoPT (Nat × Nat) Nat :=
  optD fun a => some (a.1, a)

/-- The assignment of `v` to the second component of a pair. -/
def setSnd (v : Nat) : MonoPT (Nat × Nat) Unit :=
  optD fun a => some ((), (a.1, v))

/-- The registered refinement of `addFst` by `addX`, at all equal arguments. -/
scoped instance addX_call (m n : Nat) :
    RefinesCall (addX m) (addFst n) (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot)
      (m = n) (fun _ _ _ => True) where
  refines h := by
    wrp_vcgen [addX, addFst, RegsRel]
    all_goals grind

/-- The registered refinement of `readFst` by `readX`, with equal results. -/
scoped instance readX_call :
    RefinesCall readX readFst (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot)
      True (fun v b _ => v = b) where
  refines _ := by
    wrp_vcgen [readX, readFst, RegsRel]
    all_goals grind

/-- The registration of a refinement that is a theorem. -/
scoped instance maxReg_call :
    RefinesCall maxReg (optD fun a : Nat × Nat => some (decide (a.1 < a.2), (max a.1 a.2, a.2)))
      (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot) True (fun v b _ => v = b) :=
  ⟨fun _ => refines_max⟩

/-- Two registered refinements composed by sequencing, the value of the first as the argument
    of the second. -/
theorem refines_double :
    Refines top (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot)
      (do let v ← readX; addX v) (readFst >>= addFst) (fun _ _ _ => True) := by
  wrp_steps

/-- A registered refinement composed with itself in the monad `StateM`. -/
theorem refines_max_twice :
    Refines top (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot)
      (maxReg >>= fun _ => maxReg)
      ((optD fun a : Nat × Nat => some (decide (a.1 < a.2), (max a.1 a.2, a.2))) >>= fun _ =>
        optD fun a : Nat × Nat => some (decide (a.1 < a.2), (max a.1 a.2, a.2)))
      (fun v b _ => v = b) := by
  wrp_steps

/-- A sequence nested to the left. -/
theorem refines_double_succ :
    Refines top (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot)
      ((readX >>= addX) >>= fun _ => addX 1) ((readFst >>= addFst) >>= fun _ => addFst 1)
      (fun _ _ _ => True) := by
  wrp_steps

/-- A last part that the registry lacks, left by `wrp_steps` and proved by `wrp_vcgen`. -/
theorem refines_add_copy (n : Nat) :
    Refines top (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot)
      (do addX n; let v ← readX; setY v)
      (do addFst n; let v ← readFst; setSnd v) (fun _ _ _ => True) := by
  wrp_steps
  wrp_vcgen [setY, setSnd, RegsRel]
  all_goals grind

/-- A first part that the registry lacks, sequenced at a given return relation. -/
theorem refines_set_add (n : Nat) :
    Refines top (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot)
      (setY n >>= fun _ => addX n) (setSnd n >>= fun _ => addFst n) (fun _ _ _ => True) := by
  wrp_step using fun _ _ _ => True
  · wrp_vcgen [setY, setSnd, RegsRel]
    all_goals grind
  · wrp_steps

/-- An identical first part along the identity: the continuations start from equal values. -/
theorem refines_read_add :
    Refines top Concretization.id (fun e => e)
      (readX >>= fun v => addX v) (readX >>= fun v => addX (0 + v))
      (eqRel (CPred := Regs → Prop)) := by
  wrp_steps
  rw [Nat.zero_add]
  wrp_step

/-- A sequence of `optD` steps refined by a sequence of assignments, proved by `wrp_vcgen`, which
    computes the weakest precondition of the abstract sequence. -/
theorem refines_add_four :
    Refines top (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot)
      (do addX 1; addX 1; addX 1; addX 1; pure ())
      (do addFst 1; addFst 1; addFst 1; addFst 1; pure ()) (fun _ _ _ => True) := by
  wrp_vcgen [addX, addFst, RegsRel]
  all_goals grind

end RefinementWP.StepExamples

end
