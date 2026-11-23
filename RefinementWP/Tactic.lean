/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.Compose
public import RefinementWP.Exact
public import Std.WP

/-!
# Verification conditions of a refinement: `wrp_vcgen`

A refinement `Refines top γ eps c a Q` is the lax square (`refines_top_iff`): for all abstract
postconditions `Qa` and `Ea`, the Hoare triple of the concrete program `c` with precondition
`γ.pred (wp a Qa Ea)`, postcondition `γ.post Q Qa` and exception postcondition `eps Ea`. The
tactic `wrp_vcgen` states this triple with the weakest precondition of the abstract program
computed, and applies the toolchain's `vcgen` to it.

The abstract weakest precondition is computed by instance search in `AbstractWP`: an instance
registers the weakest-precondition equation of a form of abstract program. `optD` has one, and
`pure` and `>>=` over an exact monad (`WPMonadExact`) have one each, built from the equations of
the parts, so that the weakest precondition of a sequence of `optD` steps is computed. An
abstract program without an instance keeps its `wp`, to be rewritten by the given equations.

## Main definitions

* `AbstractWP a pre`: the registered equation `wp a = pre`.
* `AbstractWP.optD`, `AbstractWP.pure`, `AbstractWP.bind`: the registered equations of `optD`,
  of `pure` and of a sequence.
* `wrp_vcgen [eqs] using [specs]`: the reduction of `Refines top γ eps c a Q` to verification
  conditions.

## Main results

* `Refines.of_triple`: the lax square as a triple of the concrete program.
* `TacticExamples.refines_swap`, `TacticExamples.refines_max`, `TacticExamples.refines_dec`:
  refinements of `optD` programs by an assignment sequence, by a branch and by a program that
  may fail, proved with `wrp_vcgen`.
-/

@[expose] public section

set_option autoImplicit false

namespace RefinementWP

open Std.WP Lean.Order

universe u v w w'

/-! ## The lax square as a triple -/

section Square

variable {CProg AProg : Type u} {CVal AVal : Type v} {CPred APred : Type w} {CE AE : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CE] [Assertion AE]
  [WP CProg CVal CPred CE] [WP AProg AVal APred AE]

/-- The registered weakest-precondition equation of the abstract program `a`: its weakest
    precondition is `pre`, which instance search computes from `a`. -/
class AbstractWP (a : AProg) (pre : outParam ((AVal → APred) → AE → APred)) : Prop where
  /-- The weakest-precondition equation. -/
  wp_eq : ∀ Qa Ea, wp a Qa Ea = pre Qa Ea

/-- An abstract program without a registered equation keeps its weakest precondition. -/
instance (priority := low) AbstractWP.self (a : AProg) : AbstractWP a (wp a) :=
  ⟨fun _ _ => rfl⟩

/-- The introduction rule of `wrp_vcgen`: refinement under `⊤` follows from the triples of the
    concrete program at the registered abstract weakest preconditions. -/
theorem Refines.of_triple [Heyting CPred] {γ : Concretization CPred APred} {eps : AE → CE}
    {c : CProg} {a : AProg} {Q : CVal → AVal → CPred} {pre : (AVal → APred) → AE → APred}
    [ha : AbstractWP a pre]
    (h : ∀ Qa Ea, Triple c (γ.pred (pre Qa Ea)) (γ.post Q Qa) (eps Ea)) :
    Refines top γ eps c a Q :=
  refines_top_iff.2 fun Qa Ea => (ha.wp_eq Qa Ea).symm ▸ (h Qa Ea).le_wp

end Square

/-- The registered weakest-precondition equation of `optD f`. -/
instance AbstractWP.optD {A B : Type} (f : A → Option (B × A)) :
    AbstractWP (RefinementWP.optD f) fun Qa _ a => match f a with
      | some p => Qa p.1 p.2
      | none => False :=
  ⟨fun Qa Ea => funext (wp_optD_apply f Qa Ea)⟩

section Exact

variable {m : Type v → Type u} [Monad m] {Pred : Type w} {EPosts : Type w'} [Assertion Pred]
  [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m]

/-- The registered weakest-precondition equation of `pure x` in an exact monad. -/
instance AbstractWP.pure {α : Type v} (x : α) :
    AbstractWP (Pure.pure x : m α) fun Q _ => Q x :=
  ⟨fun Q E => WPMonadExact.wp_pure_eq x Q E⟩

/-- The registered weakest-precondition equation of a sequence in an exact monad, from the
    equations of its parts. -/
instance AbstractWP.bind {α β : Type v} (x : m α) (f : α → m β)
    {px : (α → Pred) → EPosts → Pred} {pf : α → (β → Pred) → EPosts → Pred}
    [hx : AbstractWP x px] [hf : ∀ v, AbstractWP (f v) (pf v)] :
    AbstractWP (x >>= f) fun Q E => px (fun v => pf v Q E) E :=
  ⟨fun Q E => by
    rw [WPMonadExact.wp_bind_eq, ← hx.wp_eq]
    congr
    funext v
    exact (hf v).wp_eq Q E⟩

end Exact

namespace Concretization

variable {APred : Type} [Assertion APred] {CVal AVal : Type}

/-- The concrete postcondition over state predicates, as a function. -/
theorem post_eq_exists {σ : Type} (γ : Concretization (σ → Prop) APred)
    (Q : CVal → AVal → σ → Prop) (Qa : AVal → APred) :
    γ.post Q Qa = fun cv s => ∃ av, Q cv av s ∧ γ.pred (Qa av) s := by
  grind [post_apply]

/-- The concrete postcondition over propositions, as a function. -/
theorem post_prop_eq_exists (γ : Concretization Prop APred)
    (Q : CVal → AVal → Prop) (Qa : AVal → APred) :
    γ.post Q Qa = fun cv => ∃ av, Q cv av ∧ γ.pred (Qa av) := by
  funext cv
  simp only [post, iSup_prop_eq_exists, meet_prop_eq_and]

end Concretization

end RefinementWP

end

/-! ## The tactic -/

public meta section

namespace RefinementWP

open Lean Parser.Tactic

/--
`wrp_vcgen [eqs] using [specs]` reduces a goal `Refines top γ eps c a Q` to verification
conditions, by the lax square (`refines_top_iff`).

1. It rewrites the goal with `eqs` (definitions of the two programs, of the state relation).
2. It introduces the abstract postconditions and replaces `wp a` by the equation registered as
   an instance of `AbstractWP`, or rewrites it with `eqs`.
3. It unfolds the concretizations of the package and runs `vcgen [specs]` on the triple of `c`,
   then reduces the projections in the verification conditions.

Both lists are optional. The verification conditions and the loop invariants are the goals left.
-/
syntax (name := wrpVcgen) "wrp_vcgen" (" [" withoutPosition(simpLemma,*) "]")?
  (" using " "[" withoutPosition(simpLemma,*) "]")? : tactic

macro_rules
  | `(tactic| wrp_vcgen $[[$eqs?,*]]? $[using [$specs?,*]]?) => do
    let eqs : Array (TSyntax ``simpLemma) := (eqs?.map (·.getElems)).getD #[]
    let specs : Array (TSyntax ``simpLemma) := (specs?.map (·.getElems)).getD #[]
    let unfolds := eqs ++ #[
      ← `(simpLemma| Concretization.post_eq_exists),
      ← `(simpLemma| Concretization.post_prop_eq_exists),
      ← `(simpLemma| Concretization.ofStateRel),
      ← `(simpLemma| Concretization.id),
      ← `(simpLemma| Concretization.comp)]
    `(tactic| open _root_.Std.WP _root_.Lean.Order in (
      simp -failIfUnchanged -zeta only [$[$eqs:simpLemma],*]
      first
        | refine Refines.of_triple ?_
        | fail "wrp_vcgen: expected a goal `Refines ⊤ γ eps c a Q` over a Heyting lattice"
      intro Qa Ea
      simp -failIfUnchanged -zeta only [$[$unfolds:simpLemma],*]
      set_option experimental.vcgen true in vcgen [$[$specs:simpLemma],*]
      all_goals try dsimp only))

end RefinementWP

end

/-! ## Examples -/

@[expose] public section

namespace RefinementWP.TacticExamples

open Std.WP Lean.Order

/-- A concrete state: two registers and a temporary. -/
structure Regs where
  /-- The first register. -/
  x : Nat
  /-- The second register. -/
  y : Nat
  /-- The temporary. -/
  t : Nat

/-- The abstract state of `Regs` is the pair of the registers. -/
def RegsRel (s : Regs) (a : Nat × Nat) : Prop :=
  s.x = a.1 ∧ s.y = a.2

/-- The exchange of the registers through the temporary, an assignment sequence. -/
def swap : StateT Regs Option Unit := do
  modify fun s => { s with t := s.x }
  modify fun s => { s with x := s.y }
  modify fun s => { s with y := s.t }

/-- The maximum of the registers, written to the first, with the branch taken as result. -/
def maxReg : StateM Regs Bool := do
  let s ← get
  if s.x < s.y then
    set { s with x := s.y }
    return true
  else
    return false

/-- The decrement of a counter, which fails at zero. -/
def dec : StateT Nat Option Unit := do
  let n ← get
  if n = 0 then throw () else set (n - 1)

/-- The assignment sequence `swap` refines the exchange of a pair. -/
theorem refines_swap :
    Refines top (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot) swap
      (optD fun a : Nat × Nat => some ((), (a.2, a.1))) (fun _ _ _ => True) := by
  wrp_vcgen [swap, RegsRel]
  all_goals grind

/-- The branch `maxReg` refines the maximum of a pair. -/
theorem refines_max :
    Refines top (Concretization.ofStateRel RegsRel) (fun _ : Unit => bot) maxReg
      (optD fun a : Nat × Nat => some (decide (a.1 < a.2), (max a.1 a.2, a.2)))
      (fun v b _ => v = b) := by
  wrp_vcgen [maxReg, RegsRel]
  all_goals grind

/-- The partial program `dec` refines the predecessor, undefined at zero. -/
theorem refines_dec :
    Refines top (Concretization.ofStateRel fun s a : Nat => s = a) (fun _ : Unit => bot) dec
      (optD fun a : Nat => if a = 0 then none else some ((), a - 1)) (fun _ _ _ => True) := by
  wrp_vcgen [dec]
  all_goals grind

end RefinementWP.TacticExamples

end
