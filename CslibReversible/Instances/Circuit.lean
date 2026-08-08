/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Instances.Deterministic
import Mathlib.Logic.Equiv.Defs

/-!
# Reversible circuits

A reversible circuit is a finite sequence of gates applied to a register,
each gate a bijection of the register's states.  This is the model the
physical literature works in: Toffoli and Fredkin circuits, and the classical
skeleton of a quantum circuit, are all of this shape.

Nothing here is specific to bits.  A gate is any `Equiv.Perm W`, so `W` may be
a tuple of wires, a word, or a machine store; the circuit is reversible for
the same reason in every case, namely that each gate has an inverse.

## Why this is not `Instances.Deterministic.RevAssign`

`RevAssign` fixes an instruction set — increments and decrements of registers
with a side condition making each one injective.  A circuit takes the
bijections as given.  That is the weaker assumption and the one the physical
model actually makes: a gate is a permutation because the physics is
reversible, not because it was built out of an approved list of operations.

## Main definitions

- `Gate W`, `Circuit W`: a bijection of register states, and a list of them.
- `Conf W`: how far the circuit has run, and the register.
- `Step`, `lts`: the semantics.

## Main statements

- `bwdDeterministic`, `wellFoundedBwd`, `bStepDec`: the obligations, so that a
  circuit inherits the whole theory.
- `causal_consistency_circuit`, `unique_origin_circuit`: what it inherits.
- `origin_zero`: the start of a circuit is an origin, which is what the
  resource bounds in `Complexity.Machine` ask of a machine's initial
  configurations.
- `run`, `run_injective`: the register transformation a whole circuit effects,
  and the fact that it is injective — a circuit cannot conflate two registers,
  so whatever a circuit is used to compute, the garbage bound of
  `Complexity.Garbage` applies to what it leaves behind.
-/

universe u

namespace Cslib.LTS.RevCircuit

variable {W : Type u}

/-! ## Circuits -/

/-- A gate: any bijection of the register's states. -/
abbrev Gate (W : Type u) := Equiv.Perm W

/-- A circuit: gates applied in order. -/
abbrev Circuit (W : Type u) := List (Gate W)

/-- A configuration: how many gates have run, and the register. -/
abbrev Conf (W : Type u) := Nat × W

/--
The semantics: run the gate the counter points at, and advance.

The label is the position of the gate, which is all an observer of a
straight-line circuit can see.
-/
inductive Step (c : Circuit W) : Conf W → Nat → Conf W → Prop where
  /-- Apply the gate at the counter. -/
  | apply {i : Nat} {g : Gate W} (h : c[i]? = some g) (w : W) :
      Step c (i, w) i (i + 1, g w)

/-- A circuit as an `LTS`. -/
def lts (c : Circuit W) : LTS (Conf W) Nat := ⟨Step c⟩

@[simp] theorem lts_Tr {c : Circuit W} {p q : Conf W} {l : Nat} :
    (lts c).Tr p l q ↔ Step c p l q := Iff.rfl

/-- Everything a step tells us. -/
theorem step_inv {c : Circuit W} {p q : Conf W} {l : Nat} (h : Step c p l q) :
    ∃ g, c[l]? = some g ∧ p.1 = l ∧ q.1 = l + 1 ∧ q.2 = g p.2 := by
  cases h with | apply hg w => exact ⟨_, hg, rfl, rfl, rfl⟩

/-! ## The obligations -/

/--
**Backward determinism.**  The counter of the configuration reached says which
gate ran, and a gate is a bijection, so the configuration it ran from is
determined.
-/
instance bwdDeterministic (c : Circuit W) : BwdDeterministic (lts c) where
  bwd_unique {t u} htv htb huv hub hco := by
    rw [Transition.Valid, htb] at htv
    rw [Transition.Valid, hub] at huv
    have hs : t.src = u.src := hco
    obtain ⟨g, hg, htgt, hsrc, hw⟩ := step_inv htv
    obtain ⟨g', hg', htgt', hsrc', hw'⟩ := step_inv huv
    have hsrc1 : t.src.1 = u.src.1 := by rw [hs]
    have hl : t.lbl = u.lbl := by omega
    have hgg : g = g' := by
      rw [hl, hg'] at hg
      exact (Option.some.inj hg).symm
    have hsrc2 : t.src.2 = u.src.2 := by rw [hs]
    have htgt2 : t.tgt.2 = u.tgt.2 := by
      refine g.injective ?_
      rw [← hw, hsrc2, hw', hgg]
    exact Transition.ext hs hl (htb.trans hub.symm) (Prod.ext (by omega) htgt2)

/-- Undoing a gate decreases the counter. -/
theorem counter_lt_of_bstep {c : Circuit W} {p q : Conf W} (h : BStep (lts c) p q) :
    q.1 < p.1 := by
  obtain ⟨t, hv, hb, hs, ht⟩ := h
  subst hs; subst ht
  rw [Transition.Valid, hb] at hv
  obtain ⟨_, _, htgt, hsrc, _⟩ := step_inv hv
  omega

/-- **Well-foundedness.**  The counter is a measure for undoing. -/
instance wellFoundedBwd (c : Circuit W) : WellFoundedBwd (lts c) where
  wf := Subrelation.wf counter_lt_of_bstep (measure (fun p : Conf W => p.1)).wf

/-- A configuration with no gate before it has nothing to undo. -/
theorem origin_of_no_gate {c : Circuit W} {p : Conf W}
    (h : ∀ j, p.1 = j + 1 → c[j]? = none) : Origin (lts c) p := by
  rintro q ⟨t, hv, hb, rfl, rfl⟩
  rw [Transition.Valid, hb] at hv
  obtain ⟨g, hg, _, hsrc, _⟩ := step_inv hv
  rw [h t.lbl hsrc] at hg
  simp at hg

/-- **The start of a circuit is an origin.** -/
theorem origin_zero (c : Circuit W) (w : W) : Origin (lts c) (0, w) :=
  origin_of_no_gate (by omega)

/--
**Undoing is decidable.**  Read the counter; if a gate sits before it, run
that gate's inverse.
-/
instance bStepDec (c : Circuit W) : BStepDec (lts c) where
  step p := by
    rcases hpc : p.1 with _ | j
    · exact .inr (origin_of_no_gate (by omega))
    · rcases hg : c[j]? with _ | g
      · refine .inr (origin_of_no_gate fun j' hj' => ?_)
        have : j' = j := by omega
        rw [this]; exact hg
      · refine .inl ⟨(j, g.symm p.2),
          ⟨Transition.mk p j .bwd (j, g.symm p.2), ?_, rfl, rfl, rfl⟩⟩
        have hp : p = (j + 1, p.2) := by rw [← hpc]
        change Step c (j, g.symm p.2) j p
        rw [hp]
        have h := Step.apply (c := c) hg (g.symm p.2)
        rwa [g.apply_symm_apply] at h

/-! ## Running a circuit -/

/-- The register after the whole circuit has run. -/
def run : Circuit W → W → W
  | [], w => w
  | g :: gs, w => run gs (g w)

/-- Running a circuit is a bijection: it is a composite of bijections. -/
theorem run_injective (c : Circuit W) : Function.Injective (run c) := by
  induction c with
  | nil => exact fun _ _ h => h
  | cons g gs ih => exact fun _ _ h => g.injective (ih h)

/-! ## What a circuit inherits -/

/--
**Causal consistency for circuits.**

Nothing in the proof mentions gates: the circuit discharged backward
determinism, and the theory did the rest.
-/
theorem causal_consistency_circuit [DecidableEq W] {c : Circuit W} {p q : Conf W}
    {l₁ l₂ : List (Transition (Conf W) Nat)}
    (h₁ : Chained (lts c) p l₁ q) (h₂ : Chained (lts c) p l₂ q) :
    CEq (lts c) NoIndep p q l₁ l₂ :=
  causal_consistency_of_bwdDeterministic h₁ h₂

/-- **However a configuration is rewound, the same start is reached.** -/
theorem unique_origin_circuit [DecidableEq W] {c : Circuit W} {p o₁ o₂ : Conf W}
    (h₁ : Relation.ReflTransGen (BStep (lts c)) p o₁) (ho₁ : Origin (lts c) o₁)
    (h₂ : Relation.ReflTransGen (BStep (lts c)) p o₂) (ho₂ : Origin (lts c) o₂) :
    o₁ = o₂ :=
  unique_origin_of_bwdDeterministic h₁ ho₁ h₂ ho₂

end Cslib.LTS.RevCircuit
