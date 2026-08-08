/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Axioms
import CslibReversible.CausalEquiv

/-!
# Reversing a path

`revPath` undoes a whole path: reverse the order and reverse each transition.
It is the operation that lets the forward half of causal consistency be
obtained from the backward half by duality, instead of being proved twice.

`CEq.rev` is where the endpoint indexing shows its shape most clearly: the
statement is

```
CEq lts Indep p q l₁ l₂ → CEq lts Indep q p (revPath l₁) (revPath l₂)
```

— the endpoints *swap*.  An unindexed causal equivalence cannot say this at
all, since it does not know what its endpoints are.

The two structural axioms enter here: `IndepSymm` and `CLG`.  Reversing a
square turns the pair of independent transitions into a different pair, with
the labels exchanged, and `CLG` is exactly the statement that independence
survives that.
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}
variable {Indep : Transition State Label → Transition State Label → Prop}

/-- Undo a whole path: reverse the order, reverse each transition. -/
def revPath (l : List (Transition State Label)) : List (Transition State Label) :=
  (l.map Transition.rev).reverse

@[simp] theorem revPath_nil : revPath ([] : List (Transition State Label)) = [] := rfl

@[simp] theorem revPath_singleton (t : Transition State Label) : revPath [t] = [t.rev] := rfl

theorem revPath_append (l₁ l₂ : List (Transition State Label)) :
    revPath (l₁ ++ l₂) = revPath l₂ ++ revPath l₁ := by
  simp [revPath]

@[simp] theorem revPath_cons (t : Transition State Label) (l : List (Transition State Label)) :
    revPath (t :: l) = revPath l ++ [t.rev] := by
  simpa using revPath_append [t] l

@[simp] theorem revPath_revPath (l : List (Transition State Label)) :
    revPath (revPath l) = l := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [revPath_append, ih]

/-- Reversing a path exchanges its endpoints. -/
theorem Chained.revPath {l : List (Transition State Label)} {p q : State}
    (h : Chained lts p l q) : Chained lts q (revPath l) p := by
  induction l generalizing p with
  | nil => cases h; exact rfl
  | cons t l ih =>
    obtain ⟨hs, hv, hc⟩ := h
    have h1 : Chained lts t.tgt [t.rev] p := ⟨rfl, Transition.rev_valid hv, hs⟩
    simpa using (ih hc).append h1

/-- Reversing turns forward steps into backward ones. -/
theorem revPath_isBwd {l : List (Transition State Label)} (h : ∀ x ∈ l, x.IsFwd) :
    ∀ x ∈ revPath l, x.IsBwd := by
  intro x hx
  simp only [revPath, List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y.dir = Dir.fwd := h y hy
  simp [Transition.IsBwd, Dir.rev, hy']

/-- Reversing turns backward steps into forward ones. -/
theorem revPath_isFwd {l : List (Transition State Label)} (h : ∀ x ∈ l, x.IsBwd) :
    ∀ x ∈ revPath l, x.IsFwd := by
  intro x hx
  simp only [revPath, List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y.dir = Dir.bwd := h y hy
  simp [Transition.IsFwd, Dir.rev, hy']

theorem mem_revPath {x : Transition State Label} {s : List (Transition State Label)} :
    x ∈ revPath s ↔ ∃ z ∈ s, x = z.rev := by
  simp [revPath, List.mem_reverse, List.mem_map, eq_comm]

/-- A path cancels against its own reversal. -/
theorem cancel_path {l : List (Transition State Label)} {p q : State}
    (h : Chained lts p l q) : CEq lts Indep p p (l ++ revPath l) [] := by
  induction l generalizing p with
  | nil => simpa using CEq.refl (lts := lts) (Indep := Indep) (chained_refl p)
  | cons t l ih =>
    obtain ⟨hs, hv, hc⟩ := h
    -- (t :: l) ++ revPath l ++ [t.rev]:  cancel the inner block, then the pair.
    have inner : CEq lts Indep t.tgt t.tgt (l ++ revPath l) [] := ih hc
    have step₁ : CEq lts Indep p p ([t] ++ (l ++ revPath l) ++ [t.rev])
        ([t] ++ [] ++ [t.rev]) :=
      CEq.ctx ⟨hs, hv, rfl⟩ inner ⟨rfl, Transition.rev_valid hv, hs⟩
    have step₂ : CEq lts Indep p p [t, t.rev] [] := CEq.cancel hv hs
    have : CEq lts Indep p p ([t] ++ (l ++ revPath l) ++ [t.rev]) [] := by
      refine step₁.trans ?_
      simpa using step₂
    simpa [List.append_assoc] using this

/--
**Causal equivalence is compatible with reversal.**  Undoing two causally
equivalent paths gives two causally equivalent paths, between the swapped
endpoints.
-/
theorem CEq.rev [IndepSymm Indep] [CLG Indep] {l₁ l₂ : List (Transition State Label)}
    {p q : State} (h : CEq lts Indep p q l₁ l₂) :
    CEq lts Indep q p (revPath l₁) (revPath l₂) := by
  induction h with
  | @swap p q t u u' t' hind hu'l hu'd ht'l ht'd hcL hcR =>
    -- revPath [t, u'] = [u'.rev, t.rev] and revPath [u, t'] = [t'.rev, u.rev]
    have hcL' := hcL.revPath
    have hcR' := hcR.revPath
    have hco : (u'.rev).Coinitial (t'.rev) := by
      obtain ⟨-, -, -, -, h1⟩ := hcL
      obtain ⟨-, -, -, -, h2⟩ := hcR
      simp only [Transition.Coinitial, Transition.rev_src]
      exact h1.trans h2.symm
    have hind' : Indep u'.rev t'.rev :=
      CLG.clg (IndepSymm.symm hind) (by simp [hu'l]) (by simp [ht'l]) hco
    refine CEq.swap hind' (by simp [ht'l]) (by simp [ht'd]) (by simp [hu'l])
      (by simp [hu'd]) ?_ ?_
    · simpa using hcL'
    · simpa using hcR'
  | @cancel p t hv hs =>
    simpa using CEq.cancel (Indep := Indep) hv hs
  | @ctx p m n q pre l₁ l₂ post hpre _ hpost ih =>
    have := CEq.ctx hpost.revPath ih hpre.revPath
    simpa [revPath_append, List.append_assoc] using this
  | refl hc => exact CEq.refl hc.revPath
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Cslib.LTS
