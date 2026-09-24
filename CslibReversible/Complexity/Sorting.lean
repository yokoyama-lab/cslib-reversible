/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
import CslibReversible.Complexity.Garbage

/-!
# 比較ソートのゴミの下界

比較ソートを可逆に行うとき、出力として残さざるを得ないゴミの最小量を定める。

## 何が問題か

Axelsen–Yokoyama (APLAS 2015) は比較ソートのゴミを**置換**で表し、直接置換・階乗表現
（Lehmer 符号）・rank の 3 表現がいずれもゴミなしで相互変換できることを示した。
どれも `log₂ (n !)` ビットを達成する。同論文は下界を

> "**If we have an array of distinct elements**, the number of possible starting
> permutations is `n !`."

と、**要素が相異なるという仮定を明示して**述べている。

キーが重複するとき、繊維の大きさは階乗ではなく**多項係数**である。値域の大きさ `b` を
固定すると `log₂` 多項係数 `= Θ n` であるのに対し `log₂ (n !) = Θ (n log n)` なので、
差は定数倍ではなく `Θ (log n)` 倍に開く。したがって上の 3 表現はいずれも重複キーでは
最小でない。

## この節で定める写像

可逆実装（`experiments/multiset_rank_g.ja`、Janus）が出すのは整列済み配列そのものではなく**値ごとの個数**
`c` である。両者は同じ情報を持つ（相互に可逆・ゴミなしで移れる）ので、ここでは
`counts` を整列写像とする。実装と形式化のあいだに翻訳を挟まないためである。

## 主定理と、証明できている範囲

`card_fiber_counts` — 個数を指定したときの配置の総数が多項係数に等しい、という
**組合せ的解釈**が中核である。これは `Nat.multinomial` の docstring が主張している
ことだが、**Mathlib に定理としては存在しない**（`Multinomial.lean` にあるのは
`multinomial_spec` などの算術的性質だけ）。

本ファイルで**証明済み**なのは次である。

* `fiberWidth_counts_eq_sup` — `fiberWidth` が繊維の大きさの上限に等しい（無条件）
* `multinomial_fin_two` — 2 記号の多項係数が二項係数に等しい
* `card_fiber_counts_two` — **2 記号の場合の組合せ的解釈**（`b = 2`、無条件）
* `fiberWidth_counts_two` — したがって 2 記号のソートのゴミの下界は `max` 二項係数

一般の `b` については**未証明**である。空いている言明は下の `open problem` の節に
書いてある。実験側では `experiments/multiset_rank_ref.py` が
`(n, b) ∈ {(4,2), (4,3), (5,3), (6,2), (6,3), (6,4), (6,5), (7,3), (8,2)}` の 9 構成で
全数検査している（CI で毎回走る。層としては「有界全数検査」であって一般証明ではない）。
-/

namespace Cslib.Reversible.Sorting

open Finset

variable {n b : ℕ}

/-- 整列写像。配置 `a` を「値ごとの個数」へ送る。

個数ベクトルは整列済み配列と同じ情報を持ち、両者は可逆・ゴミなしで相互に移れる。
可逆実装 `experiments/multiset_rank_g.ja` が保持出力として残すのもこの形である。 -/
def counts (a : Fin n → Fin b) : Fin b → ℕ :=
  fun v => (univ.filter fun i => a i = v).card

/-- 個数の総和は配列の長さである。 -/
theorem sum_counts (a : Fin n → Fin b) : ∑ v, counts a v = n := by
  classical
  simpa [counts] using (Finset.card_eq_sum_card_fiberwise
    (f := a) (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin b)))
    (fun x _ => mem_univ (a x))).symm

/-- `fiberWidth` は繊維の大きさの上限そのものである。定義の展開だが、以下で
下界を「多項係数の最大値」と言い換えるときの土台になる。 -/
theorem fiberWidth_counts_eq_sup :
    fiberWidth (counts (n := n) (b := b))
      = (univ.image (counts (n := n) (b := b))).sup
          fun c => (fiber (counts (n := n) (b := b)) c).card :=
  rfl

/-- 2 記号の多項係数は二項係数である。 -/
theorem multinomial_fin_two (c : Fin 2 → ℕ) :
    Nat.multinomial univ c = (c 0 + c 1).choose (c 0) := by
  have huniv : (univ : Finset (Fin 2)) = insert 0 {1} := by decide
  rw [huniv, Nat.multinomial_insert (by decide), Nat.multinomial_singleton,
    Finset.sum_singleton, mul_one]

/-- **2 記号の場合の組合せ的解釈**。個数 `c` を持つ配置はちょうど多項係数だけある。

証明は、配置とその「値 `0` の位置の集合」を対応づける全単射による。 -/
theorem card_fiber_counts_two (c : Fin 2 → ℕ) (hc : c 0 + c 1 = n) :
    (fiber (counts (n := n) (b := 2)) c).card = Nat.multinomial univ c := by
  classical
  have h2 : ∀ x : Fin 2, x ≠ 0 → x = 1 := by decide
  have hcard : (Finset.powersetCard (c 0) (univ : Finset (Fin n))).card
      = (c 0 + c 1).choose (c 0) := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, hc]
  rw [multinomial_fin_two, ← hcard]
  -- 配置 `a` と「値 `0` が置かれた位置の集合」を対応づける。
  refine Finset.card_bij'
    (fun a _ => univ.filter fun i => a i = 0)
    (fun S _ => fun i => if i ∈ S then 0 else 1)
    ?hi ?hj ?linv ?rinv
  case hi =>
    intro a ha
    have hca : counts a = c := by simpa [fiber] using ha
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by simpa [counts] using congrFun hca 0⟩
  case hj =>
    intro S hS
    have hS' : S.card = c 0 := (Finset.mem_powersetCard.mp hS).2
    have hf0 : (univ.filter fun i => (if i ∈ S then (0 : Fin 2) else 1) = 0) = S := by
      ext i; by_cases h : i ∈ S <;> simp [h]
    have hf1 : (univ.filter fun i => (if i ∈ S then (0 : Fin 2) else 1) = 1) = Sᶜ := by
      ext i; by_cases h : i ∈ S <;> simp [h]
    have h0 : counts (fun i => if i ∈ S then (0 : Fin 2) else 1) 0 = c 0 := by
      simp only [counts]; rw [hf0]; exact hS'
    have h1 : counts (fun i => if i ∈ S then (0 : Fin 2) else 1) 1 = c 1 := by
      simp only [counts]; rw [hf1, Finset.card_compl, Fintype.card_fin, hS']; omega
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    funext v
    fin_cases v <;> assumption
  case linv =>
    intro a _
    funext i
    by_cases h : a i = 0
    · simp [h]
    · have h1 : a i = 1 := h2 (a i) h
      simp [h1]
  case rinv =>
    intro S _
    ext i
    by_cases h : i ∈ S <;> simp [h]

/-- **2 記号のソートのゴミの下界**。最小のゴミの個数は多項係数の最大値である。

`fiberWidth` は「ゴミとして持たねばならない値の個数の最小値」なので
（`Cslib.Reversible.isLeast_garbageCard`）、この式の右辺がそのまま下界を与える。 -/
theorem fiberWidth_counts_two :
    fiberWidth (counts (n := n) (b := 2))
      = (univ.image (counts (n := n) (b := 2))).sup fun c => Nat.multinomial univ c := by
  rw [fiberWidth_counts_eq_sup]
  refine Finset.sup_congr rfl ?_
  intro c hc
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hc
  have hsum : counts a 0 + counts a 1 = n := by
    rw [← Fin.sum_univ_two (counts a)]; exact sum_counts a
  exact card_fiber_counts_two _ hsum

/-!
## open problem — 一般の記号数

`b = 2` は上で証明した。**一般の `b` は未証明である。** 空いている言明は次で、
`Nat.multinomial` の組合せ的解釈そのものにあたる（Mathlib にも無い）。

```
theorem card_fiber_counts (c : Fin b → ℕ) (hc : ∑ v, c v = n) :
    (fiber (counts (n := n) (b := b)) c).card = Nat.multinomial univ c
```

見通しは 2 つある。

* **記号についての帰納**。`Nat.multinomial_cons` が
  `multinomial (cons a s) f = (f a + ∑ i ∈ s, f i).choose (f a) * multinomial s f`
  という積の形を与えるので、`b = 2` でやったのと同じ「位置の集合を選ぶ」対応を
  記号ごとに繰り返せばよい。位置の側を部分型で持ち回る手間がある
* **軌道-固定部分群**。`Equiv.Perm (Fin n)` を合成で作用させると、繊維は軌道、
  固定部分群は `Π v, Equiv.Perm {i // a i = v}` で位数 `∏ v, (c v)!`。
  `card * ∏ (c v)! = n !` が出れば `multinomial_spec` と割り算の消去で終わる

実験側は `experiments/multiset_rank_ref.py` が上に挙げた 9 構成で
全数検査しているが、これは**有界全数検査**であって一般証明ではない。
-/

end Cslib.Reversible.Sorting
