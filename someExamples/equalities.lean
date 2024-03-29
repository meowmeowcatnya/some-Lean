import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

example {a b: ℚ} {h1: a-b = 4} {h2: a*b=1} : (a+b)^2 = 20 :=
calc
  (a+b)^2 = (a-b)^2 + 4*(a*b) := by ring
    _     = 4^2 + 4*1 := by rw[h1, h2]
    _     = 20  := by ring

example {r s: ℝ} {h1: r+2*s = -1} {h2: s=3} : r=-7 :=
calc
  r = (r+2*s) - 2*s := by ring
  _ = -1 - 2*3 := by rw[h1, h2]
  _ = -7 := by ring

example {a b m n: ℤ} {h1: a*m + b*n = 1} {h2: b^2=2 * a^2} :(2 * a * n + b * m) ^ 2 = 2 :=
calc
  (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw[h1, h2]
    _ = 2 := by ring

example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) : d * (a * f - b * e) = 0 :=
calc
  d*(a*f-b*e) = a*d*f - b*d*e := by ring
  _ = b*c*f - b*d*e := by rw[h1]
  _ = b*(c*f) - b*d*e := by ring
  _ = b*(d*e) - b*d*e := by rw[h2]
  _ = 0 := by ring

example {a b: ℤ} {h1: a=2*b+5} {h2: b=3}: a=11 :=
calc
  a = 2*b+5 := by rw[h1]
  _ = 2*3+5 := by rw[h2]
  _ = 11 := by ring

example {x: ℤ} {h1: x+4=2}: x=-2 :=
calc
  x = x+4 -4 := by ring
  _ = 2 - 4 := by rw[h1]
  _ = -2 := by ring

example {a b: ℝ} {h1: a-5*b=4} {h2: b+2=3}: a=9 :=
calc
  a = a-5*b + 5*b := by ring
  _  = a-5*b + 5*(b+2-2) := by ring
  _ = 4 + 5*(3-2) := by rw[h1, h2]
  _ = 9 := by ring

example {w: ℝ} {h1: 3*w+1 = 4} : w=1 :=
calc
  w = (3*w + 1 - 1) / 3 := by ring
  _ = (4-1) / 3 := by rw[h1]
  _ = 1 := by ring

example {x: ℤ} {h1: 2*x+3=x}: x=-3 :=
calc
  x = (2*x + 3) -3 -x := by ring
  _ = x -3 -x := by rw[h1]
  _ = -3 := by ring

example {x y: ℤ} {h1:2*x-y=4} {h2:y-x+1=2} : x=5 :=
calc
  x = (2*x - y) + (y - x + 1) -1 := by ring
  _ = 4 + 2 - 1 := by rw[h1, h2]
  _ = 5 := by ring

example {u v: ℚ} {h1: u+2*v = 4} {h2: u-2*v = 6} :u=5 :=
calc
  u = ((u+2*v) + (u-2*v)) / 2 := by ring
  _ = (4 + 6) / 2 := by rw[h1, h2]
  _ = 5 := by ring

example {x y : ℝ} {h1: x+y=4} {h2: 5*x-3*y=4}: x=2 :=
calc
  x = (3*(x+y)+(5*x-3*y)) / 8 := by ring
  _ = (3*4 + 4) / 8 := by rw[h1, h2]
  _ = 2 := by ring

example {a b : ℚ} {h1: a-3 = 2*b} : a^2-a+3=4*b^2+10*b+9 :=
calc
  a^2-a+3 = (a-3)^2+5*a-6 := by ring
  _ = (a-3)^2 + 5*(a-3+3)-6 := by ring
  _ = (2*b)^2 + 5*(2*b+3)-6 := by rw[h1]
  _ = 4*b^2 + 10*b+9 := by ring

example {z: ℝ} {h1: z^2-2=0} :z^4-z^3-z^2+2*z+1 = 3 :=
calc
  z^4-z^3-z^2+2*z+1 = z^2*(z^2-2)-z^3+z^2+2*z+1 := by ring
  _ = z^2*0-z^3+z^2+2*z+1 := by rw[h1]
  _ = -z^3+z^2+2*z+1 := by ring
  _ = -z*(z^2-2)+z^2 +1 := by ring
  _ = -z*0+z^2+1 := by rw[h1]
  _ = z^2 + 1 := by ring
  _ = (z^2-2)+2 +1 := by ring
  _ = 0 + 2 + 1 := by rw[h1]
  _ = 3 := by ring

example {x y: ℤ} {h1: x+3 ≤ 2} {h2: y+2*x ≥ 3}: y > 3 :=
calc
  y = y + 2 * x - 2 *x := by ring
  _ ≥ 3 - 2 * x := by rel[h2]
  _ = 9 - 2 * (x+3) := by ring
  _ ≥ 9 - 2 * 2 := by rel[h1]
  _ = 5 := by ring
  _ > 3 := by norm_num

example {r s: ℝ} {h1: s+3 ≥ r} {h2: s+r ≤ 3}: r ≤ 3 :=
  calc
    r = (r+r)/ 2 := by ring
    _ ≤ (r+(s+3)) / 2 := by rel[h1]
    _ = ((s+r)+3) / 2 := by ring
    _ ≤ (3+3) / 2 := by rel[h2]
    _ = 3 := by norm_num

example {x y: ℝ} {h1: y≤x+5} {h2: x≤-2}: x+y ≤ 2 :=
calc
  x+y ≤ x+(x+5) := by rel[h1]
  _ ≤ (-2) + ((-2) + 5) := by rel[h2]
  _ = 1 := by norm_num
  _ ≤ 2 := by norm_num

example {u v x y A B: ℝ} {h2: A ≤ 1} {h3: B ≥ 1} {h4: x ≤ B} {h5: y ≤ B} {h6: 0 ≤ u} {h7: u ≤ A} {h8: 0 ≤ v} {h9: v < A} : u*y + v*x + u*v < 3 * A * B :=
calc
  u * y + v * x + u * v ≤ u * B + v * B + u * v := by rel[h5, h4]
    _ ≤ A * B + A * B + A * v := by rel[h7, h9]
    _ ≤ A * B + A * B + 1 * v := by rel[h2]
    _ ≤ A * B + A * B + B * v := by rel[h3]
    _ < A * B + A * B + B * A := by rel[h9]
    _ = 3 * A * B := by ring

example {t: ℝ} {h1: t ≥ 10} :t^2 - 3*t + 17 ≥ 5 :=
calc
  t^2 - 3*t + 17 = t*(t-3)+17 := by ring
  _ ≥ 10 * (10 - 3) + 17 := by rel[h1]
  _ ≥ 5 := by norm_num
