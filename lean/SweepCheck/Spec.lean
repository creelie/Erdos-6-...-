/-
The statement verified by the checker.

A sequence of blocks is a list `bs` of subsets of `{0, …, u-1}` (given by their indicator
functions).  `Admissible u h bs` collects the combinatorial rules (R1)–(R3) of the paper: every
block has two distinct elements, two elements lie together in at most one block, and every
element lies in at least `h` and at most `u - 1` blocks.  `System u h bs p t x W` is the linear
system of the paper, written out with `cnt (bs.take i) v` for the number `c_v(i)` of blocks
before the `i`-th that contain `v`.  `ParityOK bs t` is rule (R4) with the parities of the `t v`
as the witnesses.
-/
import SweepCheck.Basic

namespace SweepCheck

/-- The `i`-th block of a sequence, empty beyond its end. -/
def blk (bs : List (Nat → Bool)) (i : Nat) : Nat → Bool := (bs[i]?).getD (fun _ => false)

/-- The number of blocks of `bs` that contain `v`. -/
def cnt (bs : List (Nat → Bool)) (v : Nat) : Nat := (bs.filter (fun B => B v)).length

/-- Rules (R1) and (R2): the blocks form a linear hypergraph on `{0, …, u-1}`. -/
structure Linear (u : Nat) (bs : List (Nat → Bool)) : Prop where
  sub : ∀ i < bs.length, ∀ a, blk bs i a = true → a < u
  two : ∀ i < bs.length, ∃ a b, a ≠ b ∧ blk bs i a = true ∧ blk bs i b = true
  lin : ∀ j k, j < bs.length → k < bs.length → j ≠ k → ∀ a b, a ≠ b →
    blk bs j a = true → blk bs j b = true → blk bs k a = true → blk bs k b = true → False

/-- Rules (R1)–(R3). -/
structure Admissible (u h : Nat) (bs : List (Nat → Bool)) : Prop extends Linear u bs where
  deg : ∀ v < u, h ≤ cnt bs v ∧ cnt bs v + 1 ≤ u

/-- The linear system of the paper. -/
structure System (u h : Nat) (bs : List (Nat → Bool)) (p t x : Nat → Int) (W : Int) : Prop where
  p0 : 3 ≤ p 0
  pstep : ∀ v, v + 1 < u → p v + 2 ≤ p (v + 1)
  p1 : 2 * (u : Int) - 1 ≤ p 1
  t0 : ∀ v < u, 0 ≤ t v
  t1 : ∀ v < u, t v + 1 ≤ p v
  tmax : ∀ v < u, W ≤ t v + ((u : Int) - 1) * p v
  wlow : (h : Int) * p (u - 1) ≤ W
  x0 : 0 < bs.length → 0 ≤ x 0
  xstep : ∀ i, i + 1 < bs.length → x i + 1 ≤ x (i + 1)
  xmax : ∀ i < bs.length, x i + 1 ≤ W
  hit : ∀ i < bs.length, ∀ v < u, blk bs i v = true →
    t v + (cnt (bs.take i) v : Int) * p v = x i
  miss : ∀ i < bs.length, ∀ v < u, blk bs i v = false →
    x i + 1 ≤ t v + (cnt (bs.take i) v : Int) * p v
  last : ∀ v < u, W ≤ t v + (cnt bs v : Int) * p v

/-- Rule (R4): the parities of `t v + c_v(i)` agree within each block. -/
def ParityOK (bs : List (Nat → Bool)) (t : Nat → Int) : Prop :=
  ∀ i < bs.length, ∀ v w, blk bs i v = true → blk bs i w = true →
    (t v + (cnt (bs.take i) v : Int)) % 2 = (t w + (cnt (bs.take i) w : Int)) % 2

end SweepCheck
