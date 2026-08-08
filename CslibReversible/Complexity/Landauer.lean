/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Complexity.Garbage
import Mathlib.Data.Real.Basic

/-!
# From garbage to energy

Reversible computation is usually motivated by Landauer's principle: erasing a
bit of information dissipates at least `kT ln 2` of energy, so a computation
that never erases need not dissipate.  A machine that computes a non-injective
`f` reversibly does not erase *during* the computation, but it halts holding
garbage, and clearing that garbage — which is what has to happen before the
machine can be used again — does erase.

This file connects the two.  `Complexity.Garbage` says how many distinct
values the garbage register visits; Landauer's principle says what clearing
them costs.

## The one physical assumption

Landauer's principle is physics, and no amount of Lean makes it a theorem.  It
is therefore a **hypothesis on the statement**, `landauer` below, rather than
an axiom or an instance: it appears in the type of every result that uses it,
so no reader can mistake the energy bound for a mathematical consequence of
the definitions.

Everything else here is counting.  The split is deliberate, and it is the
whole point of the file: the boundary between "we proved this" and "physics
tells us this" should be visible in the statement, not buried in prose.

## What is *not* claimed

- **Not that the bound is attained.**  Landauer's `kT ln 2` is a
  quasi-static limit.  Erasing in finite time costs strictly more, by an amount
  that grows as the time allowed shrinks.  `landauer` is stated as a lower
  bound only, which is the direction that is safe.
- **Not that a real device is near it.**  The gap between `kT ln 2` and what
  any current technology dissipates per operation is many orders of magnitude,
  and it is not this bound that is binding in practice.
- **Not that measured surplus is provable waste.**  If a machine's garbage
  register is wider than `garbageBits f`, that is not by itself evidence of a
  wasteful design: the extra width may be separating inputs outside whatever
  set the measurement covered.  Lower bounds survive restriction of the input
  set; claims of waste do not.

## References

* R. Landauer.  *Irreversibility and heat generation in the computing
  process.*  IBM Journal of Research and Development 5(3), 183–191, 1961.
* C. H. Bennett.  *The thermodynamics of computation — a review.*
  International Journal of Theoretical Physics 21(12), 905–940, 1982.
-/

universe u v w

namespace Cslib.Reversible

variable {X : Type u} {Y : Type v} {G : Type w} [Fintype X] [DecidableEq Y] [DecidableEq G]
variable {f : X → Y}

/--
The number of bits a realization's garbage register has to be cleared through:
enough to address every value it actually visits.
-/
def bitsToClear (R : Realization f G) : ℕ :=
  Nat.clog 2 (Finset.univ.image R.garbage).card

/--
**Clearing the garbage of any realization of `f` erases at least
`garbageBits f` bits.**

Pure counting: the register visits at least `fiberWidth f` distinct values, so
addressing them takes at least `⌈log₂ (fiberWidth f)⌉` bits.
-/
theorem garbageBits_le_bitsToClear (R : Realization f G) :
    garbageBits f ≤ bitsToClear R :=
  Nat.clog_mono_right 2 (fiberWidth_le_card_image R)

/--
**The energy cost of running `f` reversibly and clearing up afterwards is at
least `garbageBits f · kT ln 2`.**

`landauer` is the physical input and the only one: it says that clearing a
register addressed by `n` bits dissipates at least `n · kTln2`.  Everything
else in the proof is `garbageBits_le_bitsToClear`.

The bound is a property of `f`, not of the machine: it mentions the
realization only to say which register is being cleared.
-/
theorem dissipation_ge (R : Realization f G) (dissipated : ℕ → ℝ) (kTln2 : ℝ)
    (hk : 0 ≤ kTln2) (landauer : ∀ n : ℕ, (n : ℝ) * kTln2 ≤ dissipated n) :
    (garbageBits f : ℝ) * kTln2 ≤ dissipated (bitsToClear R) := by
  refine le_trans ?_ (landauer (bitsToClear R))
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (garbageBits_le_bitsToClear R)) hk

/--
**An injective function can be computed with no dissipation at all**, as far
as this bound is concerned.

This is the statement reversible computing is usually motivated by, and it is
worth seeing that it comes out as the degenerate case rather than as a
separate principle: for injective `f` the garbage is empty, the counting bound
is `0`, and Landauer's principle imposes nothing.
-/
theorem dissipation_ge_zero_of_injective (hf : Function.Injective f)
    (kTln2 : ℝ) : (garbageBits f : ℝ) * kTln2 = 0 := by
  rw [garbageBits_eq_zero_iff.mpr hf]
  simp

end Cslib.Reversible
