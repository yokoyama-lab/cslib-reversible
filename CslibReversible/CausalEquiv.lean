/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Path

/-!
# Causal equivalence, indexed by its endpoints

Causal equivalence identifies two paths that differ only by permuting
independent transitions and by inserting or deleting a transition immediately
followed by its reversal.

## Why the endpoints are in the type

The obvious presentation makes causal equivalence a relation on *raw lists* of
transitions, with the endpoints supplied separately by `Chained`.  That
presentation does not support the bridging lemma

```
CEq l₁ l₂ → Chained p l₁ q → Chained p l₂ q
```

and the failure is not an artefact of the proof: `symm` applied to `cancel`
yields `CEq [] [t, t.rev]`, and the empty path is chained from every state to
itself, so the lemma would let us recover `t.src = p` from `p = q` alone.  The
Rocq development `crcore-semantics/lpu_endpoint_probe.v` refutes it outright in
a two-state model.  The practical consequence there is that chainedness has to
be threaded by hand through every intermediate lemma, and that causal
equivalence can never be quotiented.

Indexing the relation by `p` and `q` removes the problem at the source:
`cancel` carries `t.src = p`, so `symm` is harmless, and endpoint preservation
becomes the derivable `CEq.chained_left` / `CEq.chained_right` rather than an
assumption carried alongside.

It also *shortens* the presentation.  Of the eleven premises the unindexed
`swap` rule needs, seven — that `u'` starts where `t` ends, that `t'` starts
where `u` ends, that the two squares close on a common state, and the validity
of all four transitions — are exactly what the two `Chained` premises already
say.  Only the four premises that identify `u'` with `u` and `t'` with `t` as
*actions* have to be stated.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024][LPU2024]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v}

/--
Causal equivalence of paths from `p` to `q`, relative to an independence
relation `Indep` on transitions.
-/
inductive CEq (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop) :
    State → State → List (Transition State Label) → List (Transition State Label) → Prop where
  /-- Independent transitions may be performed in either order. -/
  | swap {p q : State} {t u u' t' : Transition State Label} :
      Indep t u →
      u'.lbl = u.lbl → u'.dir = u.dir →
      t'.lbl = t.lbl → t'.dir = t.dir →
      Chained lts p [t, u'] q → Chained lts p [u, t'] q →
      CEq lts Indep p q [t, u'] [u, t']
  /-- A transition immediately undone is no transition at all. -/
  | cancel {p : State} {t : Transition State Label} :
      t.Valid lts → t.src = p →
      CEq lts Indep p p [t, t.rev] []
  /-- Causal equivalence is a congruence for path composition. -/
  | ctx {p m n q : State} {pre l₁ l₂ post : List (Transition State Label)} :
      Chained lts p pre m → CEq lts Indep m n l₁ l₂ → Chained lts n post q →
      CEq lts Indep p q (pre ++ l₁ ++ post) (pre ++ l₂ ++ post)
  /-- Reflexivity, on paths. -/
  | refl {p q : State} {l : List (Transition State Label)} :
      Chained lts p l q → CEq lts Indep p q l l
  /-- Symmetry. -/
  | symm {p q : State} {l₁ l₂ : List (Transition State Label)} :
      CEq lts Indep p q l₁ l₂ → CEq lts Indep p q l₂ l₁
  /-- Transitivity. -/
  | trans {p q : State} {l₁ l₂ l₃ : List (Transition State Label)} :
      CEq lts Indep p q l₁ l₂ → CEq lts Indep p q l₂ l₃ → CEq lts Indep p q l₁ l₃

namespace CEq

variable {lts : LTS State Label} {Indep : Transition State Label → Transition State Label → Prop}
variable {p q : State} {l₁ l₂ : List (Transition State Label)}

/--
**Endpoint preservation.**  This is the statement the unindexed presentation
cannot prove.

Note that the two sides have to be established *simultaneously*: the `symm`
case exchanges them, so an induction for `Chained lts p l₁ q` alone does not
go through.  That is the same obstruction the unindexed presentation runs
into.  What makes it harmless here is `cancel` carrying `t.src = p`, so the
exchanged goal is provable rather than false.
-/
theorem chained (h : CEq lts Indep p q l₁ l₂) :
    Chained lts p l₁ q ∧ Chained lts p l₂ q := by
  induction h with
  | swap _ _ _ _ _ hc₁ hc₂ => exact ⟨hc₁, hc₂⟩
  | cancel hv hs => exact ⟨chained_cancel hv hs, rfl⟩
  | ctx hpre _ hpost ih =>
    exact ⟨by simpa using hpre.append (ih.1.append hpost),
           by simpa using hpre.append (ih.2.append hpost)⟩
  | refl hc => exact ⟨hc, hc⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

/-- Endpoint preservation, left. -/
theorem chained_left (h : CEq lts Indep p q l₁ l₂) : Chained lts p l₁ q :=
  h.chained.1

/-- Endpoint preservation, right. -/
theorem chained_right (h : CEq lts Indep p q l₁ l₂) : Chained lts p l₂ q :=
  h.chained.2

/-- Appending a path on the right respects causal equivalence. -/
theorem appendRight {n : State} {post : List (Transition State Label)}
    (h : CEq lts Indep p n l₁ l₂) (hpost : Chained lts n post q) :
    CEq lts Indep p q (l₁ ++ post) (l₂ ++ post) := by
  have := CEq.ctx (pre := []) (chained_refl (lts := lts) p) h hpost
  simpa using this

/-- Prepending a path respects causal equivalence. -/
theorem appendLeft {m : State} {pre : List (Transition State Label)}
    (hpre : Chained lts p pre m) (h : CEq lts Indep m q l₁ l₂) :
    CEq lts Indep p q (pre ++ l₁) (pre ++ l₂) := by
  have := CEq.ctx (post := []) hpre h (chained_refl (lts := lts) q)
  simpa using this

/-- Causal equivalence is a congruence for composing paths. -/
theorem comp {m : State} {k₁ k₂ : List (Transition State Label)}
    (h : CEq lts Indep p m l₁ l₂) (hk : CEq lts Indep m q k₁ k₂) :
    CEq lts Indep p q (l₁ ++ k₁) (l₂ ++ k₂) :=
  (h.appendRight hk.chained_left).trans (appendLeft h.chained_right hk)

/-- On the paths from `p` to `q`, causal equivalence is an equivalence relation. -/
theorem isEquiv :
    Equivalence (fun l₁ l₂ : {l : List (Transition State Label) // Chained lts p l q} =>
      CEq lts Indep p q l₁.val l₂.val) where
  refl l := CEq.refl l.property
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

end CEq

end Cslib.LTS
