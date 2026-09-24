#!/usr/bin/env python3
"""多重集合の配置のランキング — Janus 実装の前の参照実装。

主張: a[] (長さ n, 値域 b) -> (c[], r) は全単射である。
  c[] = 各値の個数（= 整列済み出力と同じ情報）
  r   = その多重集合の配置のうち a が辞書順で何番目か, 0 <= r < N(c)

Janus に落とすときに効くので、**除算がすべて厳密**であることも確かめる。
更新は N(c') = N(c) * (L+1) / c'[v] の一手だけで済ませる（階乗を持たない）。
"""
from math import factorial
from itertools import product


def rank_forward(a, b):
    """後ろから前へ走査して c と r を同時に組み立てる。Janus のループと同じ順序。"""
    n = len(a)
    c = [0] * b
    N = 1          # N(c) = L! / prod c!  （空の接尾辞では 1）
    r = 0
    for i in range(n - 1, -1, -1):
        v = a[i]
        c[v] += 1
        L1 = n - i                      # 新しい接尾辞の長さ
        num = N * L1
        assert num % c[v] == 0, "N の更新で割り切れない"
        N = num // c[v]
        for u in range(v):              # v より小さい値で始まる配置の総数を足す
            num2 = N * c[u]
            assert num2 % L1 == 0, "ブロック幅で割り切れない"
            r += num2 // L1
    return c, r, N


def unrank_forward(c, r, n):
    """逆向き。(c, r) -> a。Janus では uncall にあたる。"""
    c = list(c)
    b = len(c)
    N = factorial(n)
    for x in c:
        N //= factorial(x)
    a = []
    for i in range(n):
        L1 = n - i
        for v in range(b):
            if c[v] == 0:
                continue
            blk = N * c[v] // L1
            if r < blk:
                a.append(v)
                N = blk
                c[v] -= 1
                break
            r -= blk
        else:
            raise AssertionError("ランクが範囲外")
    return a


def multinomial(c):
    N = factorial(sum(c))
    for x in c:
        N //= factorial(x)
    return N


def check(n, b):
    seen = {}
    maxr = -1
    ranges = {}
    for a in product(range(b), repeat=n):
        c, r, N = rank_forward(list(a), b)
        assert N == multinomial(c), f"N が多項係数と違う {a}"
        assert 0 <= r < N, f"ランクが範囲外 {a}: {r} not in [0,{N})"
        key = (tuple(c), r)
        assert key not in seen, f"衝突: {a} と {seen[key]} が同じ (c,r)"
        seen[key] = a
        assert unrank_forward(c, r, n) == list(a), f"逆写像が戻らない {a}"
        maxr = max(maxr, r)
        ranges[tuple(c)] = N
    return len(seen), maxr + 1, max(ranges.values())


if __name__ == "__main__":
    import sys
    failed = 0
    print(f"{'n':>3} {'b':>3} {'入力数':>8} {'(c,r)の異なり':>13} {'r の値域':>9} {'max 多項係数':>12}  判定")
    for n, b in [(4, 2), (4, 3), (5, 3), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (8, 2)]:
        tot, rng, mx = check(n, b)
        ok = (tot == b ** n) and (rng == mx)
        print(f"{n:>3} {b:>3} {b**n:>8} {tot:>13} {rng:>9} {mx:>12}  {'全単射・下界一致' if ok else '×'}")
        failed += not ok
    sys.exit(1 if failed else 0)
