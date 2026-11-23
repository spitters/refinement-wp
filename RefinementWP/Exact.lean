/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.WRP
public import Std.WP

/-!
# Monads with an exact weakest precondition

The laws of `WPMonad` bound the weakest precondition of `pure x` and of `x >>= f` from below. A
monad is exact when the converse bounds hold, so that the weakest precondition of a program
built from `pure` and `>>=` is computed by the two equations. Monotone predicate transformers
form an exact monad, and so do the monads and transformers that have a `WPMonad` instance in
`Std.WP`.

## Main definitions

* `WPMonadExact m`: the weakest precondition of `m` is exact at `pure` and at `bind`.
* `MonoPT.instMonad`, `MonoPT.instWPMonad`: the monad of monotone predicate transformers and its
  weakest precondition.

## Main results

* `WPMonadExact.wp_pure_eq`, `WPMonadExact.wp_bind_eq`: the weakest-precondition equations of
  `pure` and of a sequence in an exact monad.
-/

@[expose] public section

set_option autoImplicit false

namespace RefinementWP

open Std.WP Lean.Order

universe u v w w'

/-- The weakest precondition of `m` is exact at `pure` and at `bind`: the converses of the laws
    of `WPMonad` hold. -/
class WPMonadExact (m : Type v → Type u) [Monad m] {Pred : Type w} {EPosts : Type w'}
    [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] : Prop where
  /-- The weakest precondition of `pure x` entails the postcondition at `x`. -/
  wp_pure_le {α : Type v} (x : α) (Q : α → Pred) (E : EPosts) : wp (pure x : m α) Q E ⊑ Q x
  /-- The weakest precondition of a sequence entails the composite weakest precondition. -/
  wp_bind_le {α β : Type v} (x : m α) (f : α → m β) (Q : β → Pred) (E : EPosts) :
    wp (x >>= f) Q E ⊑ wp x (fun v => wp (f v) Q E) E

/-- Monotone predicate transformers over a fixed state space form a monad under composition. -/
instance MonoPT.instMonad (A : Type) : Monad (MonoPT A) where
  pure v := ⟨fun Q => Q v, fun _ _ h => h v⟩
  bind x f := ⟨fun Q => x.trans fun v => (f v).trans Q,
    fun Q Q' h => x.mono _ _ fun v => (f v).mono Q Q' h⟩

/-- The monad laws of monotone predicate transformers. -/
instance MonoPT.instLawfulMonad (A : Type) : LawfulMonad (MonoPT A) :=
  LawfulMonad.mk' _ (id_map := fun _ => rfl) (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun _ _ _ => rfl)

/-- The weakest precondition of monotone predicate transformers is sound for `pure` and
    `bind`. -/
instance MonoPT.instWPMonad (A : Type) : WPMonad (MonoPT A) (A → Prop) Unit where
  toWP α := MonoPT.instWP A α
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ _ _ := PartialOrder.rel_refl

/-- Monotone predicate transformers are exact. -/
instance MonoPT.instWPMonadExact (A : Type) : WPMonadExact (MonoPT A) where
  wp_pure_le _ _ _ := PartialOrder.rel_refl
  wp_bind_le _ _ _ _ := PartialOrder.rel_refl

namespace WPMonadExact

section Equations

variable {m : Type v → Type u} [Monad m] {Pred : Type w} {EPosts : Type w'} [Assertion Pred]
  [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m]

/-- The weakest precondition of `pure x` in an exact monad is the postcondition at `x`. -/
theorem wp_pure_eq {α : Type v} (x : α) (Q : α → Pred) (E : EPosts) :
    wp (pure x : m α) Q E = Q x :=
  PartialOrder.rel_antisymm (wp_pure_le x Q E) (WPMonad.pure_le_wp_pure x Q E)

/-- The weakest precondition of a sequence in an exact monad is the composite weakest
    precondition. -/
theorem wp_bind_eq {α β : Type v} (x : m α) (f : α → m β) (Q : β → Pred) (E : EPosts) :
    wp (x >>= f) Q E = wp x (fun v => wp (f v) Q E) E :=
  PartialOrder.rel_antisymm (wp_bind_le x f Q E) (WPMonad.bind_le_wp_bind x f Q E)

end Equations

/-- `Id` is exact. -/
instance instId : WPMonadExact Id.{v} where
  wp_pure_le _ _ _ := PartialOrder.rel_refl
  wp_bind_le _ _ _ _ := PartialOrder.rel_refl

/-- `Option` is exact. -/
instance instOption : WPMonadExact Option.{v} where
  wp_pure_le _ _ _ := PartialOrder.rel_refl
  wp_bind_le x _ _ _ := by cases x <;> exact PartialOrder.rel_refl

/-- `Except ε` is exact. -/
instance instExcept {ε : Type v} : WPMonadExact (Except.{v, v} ε) where
  wp_pure_le _ _ _ := PartialOrder.rel_refl
  wp_bind_le x _ _ _ := by cases x <;> exact PartialOrder.rel_refl

/-- `EStateM ε σ` is exact. -/
instance instEStateM {ε σ : Type} : WPMonadExact (EStateM ε σ) where
  wp_pure_le _ _ _ := PartialOrder.rel_refl
  wp_bind_le x f Q E := by
    intro s
    simp only [WP.wp, WP.trans, bind, EStateM.bind]
    cases x s <;> grind

section Transformers

variable {m : Type v → Type u} [Monad m] {Pred : Type w} {EPosts : Type w'} [Assertion Pred]
  [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m]

/-- `StateT` preserves exactness. -/
instance instStateT {σ : Type v} : WPMonadExact (StateT σ m) where
  wp_pure_le x Q E s := wp_pure_le (m := m) (x, s) (fun p => Q p.1 p.2) E
  wp_bind_le x _ _ _ s := wp_bind_le (x.run s) _ _ _

/-- `ReaderT` preserves exactness. -/
instance instReaderT {ρ : Type v} : WPMonadExact (ReaderT ρ m) where
  wp_pure_le x Q E r := wp_pure_le (m := m) x (fun a => Q a r) E
  wp_bind_le x _ _ _ r := wp_bind_le (x.run r) _ _ _

/-- `ExceptT` preserves exactness. -/
instance instExceptT {ε : Type v} : WPMonadExact (ExceptT ε m) where
  wp_pure_le x Q E := wp_pure_le (m := m) (Except.ok x) (pushExcept Q E.fst) E.snd
  wp_bind_le x f Q E := by
    refine PartialOrder.rel_trans (wp_bind_le (m := m) x.run _ (pushExcept Q E.fst) E.snd) ?_
    apply WP.wp_monotone_post
    intro r
    cases r with
    | ok a => exact PartialOrder.rel_refl
    | error e => exact wp_pure_le (m := m) (Except.error e) (pushExcept Q E.fst) E.snd

end Transformers

/-- `OptionT` preserves exactness. -/
instance instOptionT {m : Type v → Type u} [Monad m] {Pred : Type v} {EPosts : Type w'}
    [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m] :
    WPMonadExact (OptionT m) where
  wp_pure_le x Q E := wp_pure_le (m := m) (some x) (pushOption Q E.fst) E.snd
  wp_bind_le x f Q E := by
    refine PartialOrder.rel_trans (wp_bind_le (m := m) x.run _ (pushOption Q E.fst) E.snd) ?_
    apply WP.wp_monotone_post
    intro r
    cases r with
    | some a => exact PartialOrder.rel_refl
    | none => exact wp_pure_le (m := m) none (pushOption Q E.fst) E.snd

end WPMonadExact

end RefinementWP

end
