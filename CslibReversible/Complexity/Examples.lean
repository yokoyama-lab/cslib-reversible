/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Complexity.Garbage
import Mathlib.Data.Fintype.Prod

/-!
# What the garbage bound says about gates

A definition of a resource is only worth having if it agrees with what is
already known in the cases where something is known.  This file checks
`fiberWidth` and `garbageBits` against the standard reversible gates, and
records one thing the check turns up that the usual statements do not say.

## What is checked

- `and` needs 3 garbage values, hence 2 bits.  The Toffoli construction
  `(a, b, c) ↦ (a, b, c ⊕ (a ∧ b))` run at `c = 0` keeps `(a, b)`, which is
  2 bits.  So Toffoli is optimal for `and` — in bits.
- `xor` needs 2 garbage values, hence 1 bit, and CNOT keeps exactly one input.
  So CNOT is optimal for `xor`, in bits *and* in values.
- A constant function needs the whole input kept.
- An injective function needs nothing kept — which is
  `garbageBits_eq_zero_iff`, seen on an example.

## The slack between values and bits

`and` is the smallest case where the two ways of counting disagree.  The
least number of garbage *values* is 3, but garbage is stored in bits, and
2 bits hold 4.  The missing value cannot be recovered by a cleverer gate:
any bit-addressed garbage register rounds up to a power of two.  So there
are two different optimality claims about the Toffoli gate, and only the
weaker one is true:

* optimal in bits — true, 2 bits is the minimum;
* optimal in values — false, it uses 4 where 3 suffice.

The gap is real rather than an artefact of the definition: `Fin 3` is a
perfectly good garbage type for `and` (`isLeast_garbageCard` produces one),
it is just not a register of bits.  Anything that packs several such
computations together can spend the slack — which is why the bound to quote
for a single gate is the one in values, not the one in bits.
-/

namespace Cslib.Reversible

/-! ## Conjunction -/

/-- Conjunction conflates three of its four inputs. -/
example : fiberWidth (fun p : Bool × Bool => p.1 && p.2) = 3 := by decide

/-- So it needs two bits of garbage. -/
example : garbageBits (fun p : Bool × Bool => p.1 && p.2) = 2 := by decide

/--
The Toffoli gate at `c = 0`, as a realization of `and`: it keeps both inputs.

Two bits, which the bound says is optimal.  Four values, which the bound says
is one more than necessary.
-/
def toffoliAnd : Realization (fun p : Bool × Bool => p.1 && p.2) (Bool × Bool) where
  garbage p := p
  injective := by intro p q h; exact congrArg Prod.snd h

example : Fintype.card (Bool × Bool) = 4 := by decide

/-! ## Exclusive or -/

/-- Exclusive or conflates its inputs in pairs. -/
example : fiberWidth (fun p : Bool × Bool => xor p.1 p.2) = 2 := by decide

/-- One bit of garbage, which is what CNOT keeps. -/
example : garbageBits (fun p : Bool × Bool => xor p.1 p.2) = 1 := by decide

/--
CNOT as a realization of `xor`: it keeps the control bit.

Here the two counts agree — two values, one bit — so CNOT is optimal in both
senses.
-/
def cnotXor : Realization (fun p : Bool × Bool => xor p.1 p.2) Bool where
  garbage p := p.1
  injective := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    revert h
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-! ## The extreme cases -/

variable {X : Type*} {Y : Type*} [Fintype X] [DecidableEq Y]

/--
**A constant function forces the whole input to be kept.**

Every input is in the same fiber, so the garbage must separate all of them:
a reversible machine computing a constant is a machine that stores its input.
-/
theorem fiberWidth_const [Nonempty X] (y : Y) :
    fiberWidth (fun _ : X => y) = Fintype.card X := by
  refine le_antisymm (fiberWidth_le_card_univ _) ?_
  refine le_trans (le_of_eq ?_) (card_fiber_le_fiberWidth (fun _ : X => y) y)
  rw [Fintype.card]
  exact congrArg Finset.card (Finset.filter_true_of_mem (fun _ _ => rfl)).symm

/-- An injective function needs nothing kept. -/
example : garbageBits (fun b : Bool => !b) = 0 := by
  rw [garbageBits_eq_zero_iff]
  intro a b h
  cases a <;> cases b <;> simp_all

/-! ## Three-input conjunction -/

/-- Widening the conjunction widens the worst fiber to `2^n - 1`. -/
example : fiberWidth (fun p : Bool × Bool × Bool => p.1 && p.2.1 && p.2.2) = 7 := by decide

/-- Which is three bits: nothing is saved by the rounding here. -/
example : garbageBits (fun p : Bool × Bool × Bool => p.1 && p.2.1 && p.2.2) = 3 := by decide

end Cslib.Reversible
