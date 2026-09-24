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

- **Not that the bound is attained.**  Landauer's `kT ln 2` is a quasi-static
  limit: saturating it "requires a reversible isothermal process, and hence
  infinite time" (Rolandi and Perarnau-Llobet), and the bound "is only
  achievable for infinite-time processes" (Konopik, Korten, Lutz and Linke).
  Erasing in finite time costs strictly more.  `landauer` is therefore stated
  as a lower bound only, which is the direction that stays safe.
- **Not that a real device attains it.**  "Practical erasure processes
  dissipate much more heat than the Landauer bound" (Chattopadhyay, Misra,
  Pandit and Paul).  *How much* more depends on the technology and on what one
  counts as an operation, and the two must be quoted together: a CMOS gate
  switch is `10⁴`–`10⁵` times `kT ln 2`, whereas the MANA adiabatic
  superconducting microprocessor of Ayala, Tanaka, Saito, Nozoe and Takeuchi
  switches at 1.4 zJ per junction at 4.2 K, where `kT ln 2` is 0.0402 zJ — a
  factor of about 35.  So for the reversible technologies this development is
  about, the bound is far closer to binding than for CMOS — *each measured
  against `kT ln 2` at its own operating temperature*; see the next item.
- **Not a comparison at equal temperature.**  The two factors above are taken
  at different `T`: at 300 K, `kT ln 2` is 2.87 zJ, so the 1.4 zJ of the
  4.2 K device is about 0.49 times the *room-temperature* bound, and the
  factor of 35 says nothing about which technology dissipates less.  Nor does
  it count refrigeration: removing heat at 4.2 K into a 300 K environment
  costs at least `(300 − 4.2) / 4.2 ≈ 70` joules of work per joule removed
  (the Carnot limit), and a real cryocooler does worse.  This layer bounds the
  heat released at the device, not the energy drawn at the wall.
- **Not that saving garbage bits saves proportional system energy.**  Logic
  switching is only 20–30% of a modern processor's energy (Zhirnov, Cavin and
  Gammaitoni); over half the die energy goes to caches and register files
  (Horowitz).  A bound on erased bits bounds the *logic* term, and the
  system-level saving is diluted by that term's share.  This layer says
  nothing about the wires.
- **Not that measured surplus is provable waste.**  If a machine's garbage
  register is wider than `garbageBits f`, that is not by itself evidence of a
  wasteful design: the extra width may be separating inputs outside whatever
  set the measurement covered.  Lower bounds survive restriction of the input
  set; claims of waste do not.

## References

* R. Landauer.  *Irreversibility and heat generation in the computing
  process.*  IBM Journal of Research and Development 5(3), 183–191, 1961.
  [doi:10.1147/rd.53.0183](https://doi.org/10.1147/rd.53.0183)
* C. H. Bennett.  *The thermodynamics of computation — a review.*
  International Journal of Theoretical Physics 21(12), 905–940, 1982.
  [doi:10.1007/BF02084158](https://doi.org/10.1007/BF02084158)
* A. Rolandi, M. Perarnau-Llobet.  *Finite-time Landauer principle beyond weak
  coupling.*  Quantum, 2023.
  [doi:10.22331/q-2023-11-03-1161](https://doi.org/10.22331/q-2023-11-03-1161)
* M. Konopik, T. Korten, E. Lutz, H. Linke.  *Fundamental energy cost of
  finite-time parallelizable computing.*  Nature Communications, 2023.
  [doi:10.1038/s41467-023-36020-2](https://doi.org/10.1038/s41467-023-36020-2)
* P. Chattopadhyay, A. Misra, T. Pandit, G. Paul.  *Landauer principle and
  thermodynamics of computation.*  Reports on Progress in Physics, 2025.
  [doi:10.1088/1361-6633/add6b3](https://doi.org/10.1088/1361-6633/add6b3)
* C. L. Ayala, T. Tanaka, R. Saito, M. Nozoe, N. Takeuchi.  *MANA: A Monolithic
  Adiabatic iNtegration Architecture Microprocessor Using 1.4-zJ/op Unshunted
  Superconductor Josephson Junction Devices.*  IEEE Journal of Solid-State
  Circuits, 2020.
  [doi:10.1109/JSSC.2020.3041338](https://doi.org/10.1109/JSSC.2020.3041338)
* V. V. Zhirnov, R. K. Cavin, L. Gammaitoni.  *Minimum Energy of Computing,
  Fundamental Considerations.*  In *ICT-Energy — Concepts Towards Zero-Power
  ICT*, InTech, 2014.  [doi:10.5772/57346](https://doi.org/10.5772/57346)
* M. Horowitz.  *Computing's energy problem (and what we can do about it).*
  ISSCC 2014.
  [doi:10.1109/ISSCC.2014.6757323](https://doi.org/10.1109/ISSCC.2014.6757323)
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
