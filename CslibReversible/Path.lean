/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Defs

/-!
# Paths of transitions

`Chained lts p l q` says that the list of transitions `l` is a well-formed
path from `p` to `q`: consecutive transitions meet, and each one is valid.

This is the endpoint-carrying notion that `CslibReversible.CausalEquiv` is
indexed by.
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}

/-- `Chained lts p l q`: the transitions `l` form a valid path from `p` to `q`. -/
def Chained (lts : LTS State Label) : State → List (Transition State Label) → State → Prop
  | p, [], q => p = q
  | p, t :: l, q => t.src = p ∧ t.Valid lts ∧ Chained lts t.tgt l q

@[simp] theorem chained_nil {p q : State} :
    Chained lts p [] q ↔ p = q := Iff.rfl

@[simp] theorem chained_cons {p q : State} {t : Transition State Label}
    {l : List (Transition State Label)} :
    Chained lts p (t :: l) q ↔ t.src = p ∧ t.Valid lts ∧ Chained lts t.tgt l q :=
  Iff.rfl

theorem chained_refl (p : State) : Chained lts p [] p := rfl

/-- Paths compose. -/
theorem Chained.append {l₁ l₂ : List (Transition State Label)} {p m q : State}
    (h₁ : Chained lts p l₁ m) (h₂ : Chained lts m l₂ q) :
    Chained lts p (l₁ ++ l₂) q := by
  induction l₁ generalizing p with
  | nil => cases h₁; exact h₂
  | cons t l ih =>
    obtain ⟨hs, hv, hc⟩ := h₁
    exact ⟨hs, hv, ih hc⟩

/-- Paths decompose. -/
theorem Chained.split {l₁ l₂ : List (Transition State Label)} {p q : State}
    (h : Chained lts p (l₁ ++ l₂) q) :
    ∃ m, Chained lts p l₁ m ∧ Chained lts m l₂ q := by
  induction l₁ generalizing p with
  | nil => exact ⟨p, rfl, h⟩
  | cons t l ih =>
    obtain ⟨hs, hv, hc⟩ := h
    obtain ⟨m, hm₁, hm₂⟩ := ih hc
    exact ⟨m, ⟨hs, hv, hm₁⟩, hm₂⟩

theorem Chained.append_iff {l₁ l₂ : List (Transition State Label)} {p q : State} :
    Chained lts p (l₁ ++ l₂) q ↔ ∃ m, Chained lts p l₁ m ∧ Chained lts m l₂ q :=
  ⟨Chained.split, fun ⟨_, h₁, h₂⟩ => h₁.append h₂⟩

/-- A one-step path is exactly a valid transition. -/
theorem chained_singleton {p q : State} {t : Transition State Label} :
    Chained lts p [t] q ↔ t.src = p ∧ t.Valid lts ∧ t.tgt = q := by
  simp [Chained]

/-- A transition immediately followed by its reversal is a loop. -/
theorem chained_cancel {p : State} {t : Transition State Label}
    (hv : t.Valid lts) (hs : t.src = p) : Chained lts p [t, t.rev] p := by
  refine ⟨hs, hv, ?_, Transition.rev_valid hv, ?_⟩
  · simp
  · simpa using hs

end Cslib.LTS
