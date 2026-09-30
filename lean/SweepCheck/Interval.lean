/-
Good intervals, primes, and the counting argument.

`Good P N W` says that none of the integers `N+1, …, N+W` is divisible by exactly one element of
the list `P`.  The run lemma is the counting argument of the paper: the multiples of the smallest
prime `p₁` of `P` in a good interval are `p₁ t` for consecutive integers `t`, and each such `t` is
divisible by another prime of `P`.
-/
import SweepCheck.Count

namespace SweepCheck

/-- `p` is a prime. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- None of the integers `N+1, …, N+W` is divisible by exactly one element of `P`. -/
def Good (P : List Nat) (N W : Nat) : Prop :=
  ∀ x, N < x → x ≤ N + W → P.countP (fun p => x % p == 0) ≠ 1

/-- A primality test. -/
def isPrimeB (n : Nat) : Bool := decide (2 ≤ n) && (List.range n).all (fun d => d < 2 || n % d != 0)

theorem isPrimeB_of_isPrime {n : Nat} (hn : IsPrime n) : isPrimeB n = true := by
  unfold isPrimeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨hn.1, fun d hd => ?_⟩
  by_cases h2 : d < 2
  · exact Or.inl (by simp [h2])
  · right
    intro h0
    rcases hn.2 d (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega

theorem IsPrime.pos {p : Nat} (hp : IsPrime p) : 0 < p := by have := hp.1; omega

theorem IsPrime.odd {p : Nat} (hp : IsPrime p) (h2 : p ≠ 2) : p % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · rcases hp.2 2 (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega
  · exact h

theorem coprime_of_primes {p q : Nat} (hp : IsPrime p) (hq : IsPrime q) (hpq : p ≠ q) :
    Nat.Coprime p q := by
  have h1 : Nat.gcd p q ∣ p := Nat.gcd_dvd_left p q
  have h2 : Nat.gcd p q ∣ q := Nat.gcd_dvd_right p q
  rcases hp.2 _ h1 with h | h
  · exact h
  · rw [h] at h2
    rcases hq.2 _ h2 with h' | h'
    · have := hp.1; omega
    · exact absurd h' hpq

/-- A good interval contains good intervals of every smaller length. -/
theorem Good.mono {P : List Nat} {N W W' : Nat} (hg : Good P N W) (hW : W' ≤ W) : Good P N W' :=
  fun x h1 h2 => hg x h1 (by omega)

/-- The run lemma.  Let `P = p₁ :: Q` be sorted primes and let `N+1, …, N+L` be good.  If
`p₁ K ≤ L`, then each of the `K` consecutive integers `N / p₁ + 1 + i`, `i < K`, is divisible by
some element of `Q`. -/
theorem run_cover {p1 : Nat} {Q : List Nat} (hp : ∀ q ∈ p1 :: Q, IsPrime q)
    (hs : (p1 :: Q).Pairwise (· < ·)) {N L K : Nat} (hg : Good (p1 :: Q) N L) (hK : p1 * K ≤ L) :
    ∀ i < K, ∃ q ∈ Q, (N / p1 + 1 + i) % q = 0 := by
  intro i hi
  have hp1 := hp p1 List.mem_cons_self
  have hpos := hp1.pos
  -- the multiple `p₁ (N / p₁ + 1 + i)` lies in the interval
  have hlo : N < p1 * (N / p1 + 1 + i) := by
    have := Nat.lt_mul_div_succ N hpos
    have : p1 * (N / p1 + 1) ≤ p1 * (N / p1 + 1 + i) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hhi : p1 * (N / p1 + 1 + i) ≤ N + L := by
    have e : p1 * (N / p1 + 1 + i) = p1 * (N / p1) + p1 * (i + 1) := by
      rw [show N / p1 + 1 + i = N / p1 + (i + 1) by omega, Nat.mul_add]
    have h1 := Nat.mul_div_le N p1
    have h2 : p1 * (i + 1) ≤ p1 * K := Nat.mul_le_mul_left _ (by omega)
    omega
  have hc := hg _ hlo hhi
  rw [List.countP_cons] at hc
  have hself : (p1 * (N / p1 + 1 + i) % p1 == 0) = true := by simp [Nat.mul_mod_right]
  rw [if_pos hself] at hc
  have hpos' : 0 < Q.countP (fun p => p1 * (N / p1 + 1 + i) % p == 0) := by omega
  obtain ⟨q, hq, hqd⟩ := List.countP_pos_iff.mp hpos'
  refine ⟨q, hq, ?_⟩
  simp only [beq_iff_eq] at hqd
  have hqp : IsPrime q := hp q (List.mem_cons_of_mem _ hq)
  have hlt : p1 < q := List.rel_of_pairwise_cons hs hq
  have hcop : Nat.Coprime q p1 := coprime_of_primes hqp hp1 (by omega)
  exact Nat.mod_eq_zero_of_dvd (hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hqd))

/-- The counting form of the run lemma: `K ≤ ∑_{q ∈ Q} b_q`, where `b_q` counts the multiples of
`q` in the run and satisfies `b_q q ≤ K + q - 1`. -/
theorem run_count {p1 : Nat} {Q : List Nat} (hp : ∀ q ∈ p1 :: Q, IsPrime q)
    (hs : (p1 :: Q).Pairwise (· < ·)) {N L K : Nat} (hg : Good (p1 :: Q) N L) (hK : p1 * K ≤ L) :
    K ≤ (Q.map (fun q => below K (fun i => (N / p1 + 1 + i) % q == 0))).sum := by
  have hcov := run_cover hp hs hg hK
  have := length_le_sum Q (fun q i => (N / p1 + 1 + i) % q == 0) (List.range K) (by
    intro a ha
    obtain ⟨q, hq, h0⟩ := hcov a (List.mem_range.mp ha)
    exact ⟨q, hq, by simp [h0]⟩)
  simpa [below] using this

theorem sum_map_one (Q : List Nat) : (Q.map (fun _ => 1)).sum = Q.length := by
  induction Q with
  | nil => rfl
  | cons q Q ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

/-- Separation: if the second prime is large, a good interval is shorter than `p₁ p₂`. -/
theorem short_of_big {p1 p2 : Nat} {R : List Nat} (hp : ∀ q ∈ p1 :: p2 :: R, IsPrime q)
    (hs : (p1 :: p2 :: R).Pairwise (· < ·)) {N W : Nat} (hg : Good (p1 :: p2 :: R) N W)
    (hbig : R.length + 2 ≤ p2) : W < p1 * p2 := by
  apply Nat.lt_of_not_le
  intro hW
  have hc := run_count hp hs hg hW
  have hle : ((p2 :: R).map (fun q => below p2 (fun i => (N / p1 + 1 + i) % q == 0))).sum ≤
      ((p2 :: R).map (fun _ => 1)).sum := by
    apply sum_map_le
    intro q hq
    have hqp := (hp q (List.mem_cons_of_mem _ hq)).pos
    have hq2 : p2 ≤ q := by
      rcases List.mem_cons.mp hq with h | h
      · omega
      · exact Nat.le_of_lt (List.rel_of_pairwise_cons (List.Pairwise.of_cons hs) h)
    have hb := below_dvd_le (N / p1 + 1) q p2 hqp
    have : below p2 (fun i => (N / p1 + 1 + i) % q == 0) * q < 2 * q := by omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  rw [sum_map_one] at hle
  simp only [List.length_cons] at hle
  omega

end SweepCheck
