/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Complexity.Machine
import CslibReversible.Complexity.Examples
import CslibReversible.Instances.Deterministic
import Mathlib.Data.Fintype.Prod

/-!
# A machine that pays the bound

`Complexity.Machine` says every reversible machine computing `f` halts holding
at least `fiberWidth f` distinguishable residues.  A lower bound that no
machine meets would be a bound about nothing, so this file exhibits a machine
and computes both sides.

The machine is the Toffoli gate, run once, on three wires with the third set
to `false`.  It computes conjunction, and it halts holding both inputs.

```
(a, b, false)  ↦  (a, b, a ∧ b)
```

## What the two sides come to

`fiberWidth (· ∧ ·) = 3` and the residue `(a, b)` ranges over 4 values, so the
bound is met with one value to spare.  As `Complexity.Examples` records, that
spare value cannot be recovered by any gate whose garbage is a register of
bits: 3 does not fit in fewer than 2 bits, and 2 bits hold 4.

## What instantiating the definition changed

`Computes` originally asked for a readout injective on the whole state space.
No machine with a control state can supply that: this one has a stage bit that
says whether the gate has run, and the stage carries no information once the
machine has halted, yet an everywhere-injective readout would have to keep it
and charge it to the garbage.  The requirement is now injectivity on the
configurations the machine actually halts in, which is all the proof ever
used.
-/

namespace Cslib.Reversible.ToffoliMachine

open Cslib.LTS Cslib.Reversible

/-! ## The machine -/

/-- Three wires. -/
abbrev Wires := Bool × Bool × Bool

/-- The Toffoli gate: flip the third wire exactly when the first two are set. -/
def gate (w : Wires) : Wires := (w.1, w.2.1, xor w.2.2 (w.1 && w.2.1))

theorem gate_involutive : Function.Involutive gate := by
  rintro ⟨a, b, c⟩
  revert a b c
  decide

/-- A configuration: whether the gate has run, and the wires. -/
abbrev Conf := Bool × Wires

/--
The semantics.  There is one step: run the gate.

The label is `Unit` — a single-gate machine gives an observer nothing to
distinguish steps by.
-/
inductive Step : Conf → Unit → Conf → Prop where
  /-- Run the gate. -/
  | run (w : Wires) : Step (false, w) () (true, gate w)

/-- The machine as an `LTS`. -/
def lts : LTS Conf Unit := ⟨Step⟩

@[simp] theorem lts_Tr {p q : Conf} {l : Unit} : lts.Tr p l q ↔ Step p l q := Iff.rfl

/-- Everything a step tells us. -/
theorem step_inv {p q : Conf} {l : Unit} (h : Step p l q) :
    p.1 = false ∧ q.1 = true ∧ q.2 = gate p.2 := by
  cases h with | run w => exact ⟨rfl, rfl, rfl⟩

/-! ## Discharging the obligations -/

/--
**Backward determinism.**  A configuration that the gate has run into
determines the configuration it ran from, because the gate is an involution.
-/
instance bwdDeterministic : BwdDeterministic lts where
  bwd_unique {t u} htv htb huv hub hco := by
    rw [Transition.Valid, htb] at htv
    rw [Transition.Valid, hub] at huv
    obtain ⟨_, _, hg⟩ := step_inv htv
    obtain ⟨_, _, hg'⟩ := step_inv huv
    have hsrc : t.src = u.src := hco
    have hw : t.tgt.2 = u.tgt.2 := by
      have : gate t.tgt.2 = gate u.tgt.2 := by rw [← hg, ← hg', hsrc]
      exact gate_involutive.injective this
    refine Transition.ext hsrc rfl (htb.trans hub.symm) (Prod.ext ?_ hw)
    obtain ⟨h1, _, _⟩ := step_inv htv
    obtain ⟨h2, _, _⟩ := step_inv huv
    rw [h1, h2]

/-- Undoing takes the stage from `true` to `false`, so it cannot go on. -/
theorem stage_false_of_bstep {p q : Conf} (h : BStep lts p q) : q.1 = false := by
  obtain ⟨t, hv, hb, hs, ht⟩ := h
  subst hs; subst ht
  rw [Transition.Valid, hb] at hv
  exact (step_inv hv).1

/-- A configuration whose gate has not run has nothing to undo. -/
theorem origin_of_stage_false {p : Conf} (h : p.1 = false) : Origin lts p := by
  rintro q ⟨t, hv, hb, rfl, rfl⟩
  rw [Transition.Valid, hb] at hv
  obtain ⟨_, htrue, _⟩ := step_inv hv
  rw [h] at htrue
  exact Bool.noConfusion htrue

/-- **Well-foundedness.**  A second undo would have to start from stage `false`. -/
instance wellFoundedBwd : WellFoundedBwd lts where
  wf := ⟨fun p => Acc.intro p fun q hq => Acc.intro q fun r hr =>
    absurd hr (origin_of_stage_false (stage_false_of_bstep hq) r)⟩

/-- **Undoing is decidable.**  At stage `true` the gate ran; otherwise it did not. -/
instance bStepDec : BStepDec lts where
  step := by
    rintro ⟨s, w⟩
    cases s
    · exact .inr (origin_of_stage_false rfl)
    · refine .inl ⟨(false, gate w),
        ⟨Transition.mk (true, w) () .bwd (false, gate w), ?_, rfl, rfl, rfl⟩⟩
      change Step (false, gate w) () (true, w)
      have h := Step.run (gate w)
      rwa [gate_involutive w] at h

/-! ## The machine computes conjunction -/

/-- The function the machine computes. -/
def conj (p : Bool × Bool) : Bool := p.1 && p.2

/-- The Toffoli gate, run once from a cleared third wire, computing `conj`. -/
def computes : Computes lts conj (Bool × Bool) where
  input p := (false, (p.1, p.2, false))
  input_injective := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.1 h.2.2.1
  input_origin _ := origin_of_stage_false rfl
  final p := (true, gate (p.1, p.2, false))
  rewinds p := .single ⟨Transition.mk _ () .bwd _, Step.run _, rfl, rfl, rfl⟩
  readout c := (c.2.2.2, (c.2.1, c.2.2.1))
  readout_injOn := by
    rintro _ ⟨⟨a, b⟩, rfl⟩ _ ⟨⟨c, d⟩, rfl⟩ h
    revert h
    cases a <;> cases b <;> cases c <;> cases d <;> simp [gate]
  readout_fst := by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-! ## Both sides of the bound -/

/-- The machine halts holding four distinguishable residues. -/
example : Fintype.card (Bool × Bool) = 4 := by decide

/-- Conjunction needs three. -/
example : fiberWidth conj = 3 := by decide

/--
**The bound holds for this machine**, as `Complexity.Machine` says it must —
and it is not tight, by exactly the one value that a register of bits cannot
spend.
-/
example : fiberWidth conj ≤ Fintype.card (Bool × Bool) :=
  Computes.fiberWidth_le_card (Indep := NoIndep) computes

/-- In bits the machine is optimal: two bits held, two bits needed. -/
example : garbageBits conj = 2 := by decide

end Cslib.Reversible.ToffoliMachine
