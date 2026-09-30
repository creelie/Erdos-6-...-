/-
The upper bounds for one to eight primes.

`upper_bounds` states: for `1 ≤ u ≤ 8`, every good interval of a set of `u` primes is shorter than
`h(u)` times the largest prime, where `h(1), …, h(8) = 1, 2, 2, 3, 2, 4, 3, 4`.  Sets whose second
prime is below `2u - 1` are handled by `smallOK`, which the kernel evaluates; all other sets by the
sweep, through the hypothesis `hlog` that the checker accepts the proof logs.  The executable
`sweepcheck` evaluates `checkLog` on the logs.
-/
import SweepCheck.Sound
import SweepCheck.Reduction
import SweepCheck.Small

namespace SweepCheck

/-- The values `h(1), …, h(8)`. -/
def hval : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 2
  | 6 => 4
  | 7 => 3
  | 8 => 4
  | _ => 0

theorem hval_ge_two : ∀ u < 9, 2 ≤ u → 2 ≤ hval u := by decide

/-- The search over sets with a small second prime, evaluated by the kernel. -/
theorem small_ok : ∀ u < 9, 3 ≤ u → smallOK u (hval u) = true := by decide +kernel

theorem pr_len_eq_lastD : ∀ (a : Nat) (l : List Nat), l ≠ [] → pr (a :: l) l.length = lastD l
  | _, [], h => absurd rfl h
  | _, [_], _ => rfl
  | _, b :: c :: l, _ => pr_len_eq_lastD b (c :: l) (by simp)

/-- The sweep, for sets whose second prime is at least `2u - 1`. -/
theorem sweep_upper (u h : Nat) (d : ByteArray) (hd : checkLog u h d = true) (hu : 2 ≤ u)
    (hh : 2 ≤ h) (P : List Nat) (hlen : P.length = u) (hp : ∀ p ∈ P, IsPrime p)
    (hs : P.Pairwise (· < ·)) (hbig : 2 * u - 1 ≤ pr P 1) (N W : Nat) (hg : Good P N W) :
    W < h * pr P (u - 1) := by
  apply Nat.lt_of_not_le
  intro hW
  have st : Setup u h P N W := ⟨hlen, hu, hp, hs, hg, hh, hW, hbig⟩
  exact checkLog_sound u h hu d hd _ _ _ _ _ st.admissible st.system st.parity

/-- A single prime: a good interval contains no multiple of it. -/
theorem one_upper (p : Nat) (hp : IsPrime p) (N W : Nat) (hg : Good [p] N W) : W < p := by
  apply Nat.lt_of_not_le
  intro hW
  have hpos := hp.pos
  have hlo : N < p * (N / p + 1) := Nat.lt_mul_div_succ N hpos
  have hhi : p * (N / p + 1) ≤ N + W := by
    have := Nat.mul_div_le N p
    rw [Nat.mul_add, Nat.mul_one]; omega
  have := hg _ hlo hhi
  simp [Nat.mul_mod_right] at this

/-- The upper bounds of the main theorem. -/
theorem upper_bounds (log : Nat → ByteArray)
    (hlog : ∀ u, 2 ≤ u → u ≤ 8 → checkLog u (hval u) (log u) = true)
    (u : Nat) (hu1 : 1 ≤ u) (hu8 : u ≤ 8) (P : List Nat) (hlen : P.length = u)
    (hp : ∀ p ∈ P, IsPrime p) (hs : P.Pairwise (· < ·)) (m : Nat) (hm : m ∈ P)
    (hmax : ∀ p ∈ P, p ≤ m) (N W : Nat) (hg : Good P N W) : W < hval u * m := by
  match P, hlen, hp, hs, hm, hmax, hg with
  | [p], hlen, hp, _, hm, _, hg =>
    simp only [List.length_cons, List.length_nil] at hlen
    subst hlen
    simp only [List.mem_singleton] at hm
    subst hm
    simpa [hval] using one_upper m (hp m (by simp)) N W hg
  | p1 :: p2 :: R, hlen, hp, hs, hm, hmax, hg =>
    simp only [List.length_cons] at hlen
    have hu : 2 ≤ u := by omega
    -- the largest prime is the last one
    have hs2 : (p2 :: R).Pairwise (· < ·) := List.Pairwise.of_cons hs
    have h12 : p1 < p2 := List.rel_of_pairwise_cons hs (by simp)
    have hlast : lastD (p2 :: R) = m := by
      apply Nat.le_antisymm
      · exact hmax _ (List.mem_cons_of_mem _ (lastD_mem (by simp)))
      · rcases List.mem_cons.mp hm with h | h
        · have := le_lastD hs2 p2 (by simp)
          omega
        · exact le_lastD hs2 m h
    have hp2 := hp p2 (by simp)
    have hp1 := hp p1 (by simp)
    by_cases hbig : 2 * u - 1 ≤ p2
    · -- the sweep
      have hpr1 : pr (p1 :: p2 :: R) 1 = p2 := rfl
      have hlast' : pr (p1 :: p2 :: R) (u - 1) = m := by
        rw [← hlast, show u - 1 = (p2 :: R).length by simp; omega]
        exact pr_len_eq_lastD p1 (p2 :: R) (by simp)
      rw [← hlast']
      exact sweep_upper u (hval u) (log u) (hlog u hu hu8) hu (hval_ge_two u (by omega) hu)
        _ (by simp [hlen]) hp hs (by rw [hpr1]; exact hbig) N W hg
    · -- a small second prime
      have hodd : p2 ≠ 2 * u - 2 := by
        intro e
        have := hp1.1
        have := hp2.odd (by omega)
        omega
      have hu3 : 3 ≤ u := by have := hp1.1; omega
      rw [← hlast]
      exact smallOK_sound u (hval u) (small_ok u (by omega) hu3) hu3 p1 p2 R (by omega) hp hs
        (by omega) N W hg

end SweepCheck
