import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic

example {a b: ℝ} {h1: a-5*b=4} {h2: b+2=3}: a=9 := by
  have hb: b=1 := by linarith
  calc
    a = a - 5*b + 5*b := by ring
    _ = 4 + 5*1 := by rw[h1, hb]
    _ = 9 := by norm_num

example {m n: ℤ} {h1: m+3≤2*n-1} {h2: n≤5}: m≤6 := by
  have h3: m+3 ≤ 9 := by linarith
  linarith[h3]

example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by linarith[h1]
  have h4 : r ≤ 3 - s := by linarith[h2]
  calc
    r = (r + r) / 2 := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by rel[h3, h4]
    _ = 3 := by norm_num


/- I gave up on this one
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3: t=3 :=
    calc
      t * t = t ^ 2 := by ring
      _ = 3 * t := by rw [h1]
      simp
-/
