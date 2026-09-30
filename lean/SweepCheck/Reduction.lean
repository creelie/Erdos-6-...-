/-
From a long good interval to a solution of the sweep system.

Let `P` be a sorted list of `u ≥ 2` primes whose second element is at least `2u - 1`, and let
`N+1, …, N+W` be a good interval with `W ≥ h p_u` for some `h ≥ 2`.  The points of the interval
(the positions `j < W` for which some prime of `P` divides `N+1+j`), their blocks (the ranks of the
primes dividing them) and the positions `t_v` of the first multiples satisfy (R1)–(R4) and the
linear system of `SweepCheck.Spec`.
-/
import SweepCheck.Interval
import SweepCheck.Lemmas

namespace SweepCheck

/-- The element of rank `v` of `P`. -/
def pr (P : List Nat) (v : Nat) : Nat := P.getD v 0

theorem countP_eq_below (P : List Nat) (f : Nat → Bool) :
    P.countP f = below P.length (fun v => f (pr P v)) := by
  have hmap : (List.range P.length).map (pr P) = P := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [pr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  conv => lhs; rw [← hmap]
  rw [List.countP_map, List.countP_eq_length_filter]
  rfl

/-- The hypotheses of the reduction. -/
structure Setup (u h : Nat) (P : List Nat) (N W : Nat) : Prop where
  len : P.length = u
  two : 2 ≤ u
  prime : ∀ p ∈ P, IsPrime p
  sorted : P.Pairwise (· < ·)
  good : Good P N W
  hh : 2 ≤ h
  long : h * pr P (u - 1) ≤ W
  big : 2 * u - 1 ≤ pr P 1

section
variable {u h : Nat} {P : List Nat} {N W : Nat} (hs : Setup u h P N W)
include hs

theorem Setup.pr_eq {v : Nat} (hv : v < u) : pr P v = P[v]'(by rw [hs.len]; exact hv) := by
  simp [pr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hs.len ▸ hv)]

theorem Setup.pr_prime {v : Nat} (hv : v < u) : IsPrime (pr P v) := by
  rw [hs.pr_eq hv]; exact hs.prime _ (List.getElem_mem _)

theorem Setup.pr_pos {v : Nat} (hv : v < u) : 0 < pr P v := (hs.pr_prime hv).pos

theorem Setup.pr_lt {v w : Nat} (hvw : v < w) (hw : w < u) : pr P v < pr P w := by
  rw [hs.pr_eq (by omega), hs.pr_eq hw]
  exact List.pairwise_iff_getElem.mp hs.sorted v w _ _ hvw

theorem Setup.pr_le {v w : Nat} (hvw : v ≤ w) (hw : w < u) : pr P v ≤ pr P w := by
  rcases Nat.lt_or_eq_of_le hvw with h | h
  · exact Nat.le_of_lt (hs.pr_lt h hw)
  · rw [h]; exact Nat.le_refl _

theorem Setup.good_idx {j : Nat} (hj : j < W) :
    below u (fun v => (N + 1 + j) % pr P v == 0) ≠ 1 := by
  have := hs.good (N + 1 + j) (by omega) (by omega)
  rwa [countP_eq_below, hs.len] at this

/-- The first prime is odd. -/
theorem Setup.odd {v : Nat} (hv : v < u) (h3 : 3 ≤ pr P 0) : pr P v % 2 = 1 :=
  (hs.pr_prime hv).odd (by have := hs.pr_le (Nat.zero_le v) hv; omega)

/-- The separation lemma: the interval is shorter than `p₁ p₂`. -/
theorem Setup.short : W < pr P 0 * pr P 1 := by
  obtain ⟨hlen, hu, hp, hsort, hg, _, _, hbig⟩ := hs
  match P, hlen with
  | [], hlen => simp at hlen; omega
  | [_], hlen => simp at hlen; omega
  | p1 :: p2 :: R, hlen =>
    simp only [List.length_cons] at hlen
    exact short_of_big hp hsort hg (by simp only [pr, List.getD_cons_succ, List.getD_cons_zero] at hbig; omega)

/-- Two primes of `P` do not share two multiples in the interval. -/
theorem Setup.sep {a b j k : Nat} (hab : a ≠ b) (ha : a < u) (hb : b < u) (hjk : j < k) (hk : k < W)
    (h1 : (N + 1 + j) % pr P a = 0) (h2 : (N + 1 + j) % pr P b = 0)
    (h3 : (N + 1 + k) % pr P a = 0) (h4 : (N + 1 + k) % pr P b = 0) : False := by
  have hcop : Nat.Coprime (pr P a) (pr P b) := by
    apply coprime_of_primes (hs.pr_prime ha) (hs.pr_prime hb)
    intro e
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · have := hs.pr_lt h hb; omega
    · have := hs.pr_lt h ha; omega
  have hj := hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
  have hk' := hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h3) (Nat.dvd_of_mod_eq_zero h4)
  have hd : pr P a * pr P b ∣ k - j := by
    have := Nat.dvd_sub hk' hj
    rwa [show N + 1 + k - (N + 1 + j) = k - j by omega] at this
  have hle := Nat.le_of_dvd (by omega) hd
  have h01 : pr P 0 * pr P 1 ≤ pr P a * pr P b := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact Nat.mul_le_mul (hs.pr_le (Nat.zero_le a) ha) (hs.pr_le (by omega) hb)
    · rw [Nat.mul_comm (pr P 0)]
      exact Nat.mul_le_mul (hs.pr_le (by omega) ha) (hs.pr_le (Nat.zero_le b) hb)
  have := hs.short
  omega

end

/-! ### Points and blocks -/

/-- Position `j` is a point: some prime of `P` divides `N+1+j`. -/
def isPt (u : Nat) (P : List Nat) (N j : Nat) : Bool :=
  (List.range u).any (fun v => (N + 1 + j) % pr P v == 0)

/-- The block of position `j`: the ranks of the primes dividing `N+1+j`. -/
def blockAt (u : Nat) (P : List Nat) (N j : Nat) : Nat → Bool :=
  fun v => decide (v < u) && ((N + 1 + j) % pr P v == 0)

/-- The points of the interval, in increasing order. -/
def pts (u : Nat) (P : List Nat) (N W : Nat) : List Nat := (List.range W).filter (isPt u P N)

/-- The blocks of the interval, in the order of their points. -/
def blocks (u : Nat) (P : List Nat) (N W : Nat) : List (Nat → Bool) :=
  (pts u P N W).map (blockAt u P N)

theorem cnt_single (B : Nat → Bool) (v : Nat) : cnt [B] v = if B v then 1 else 0 := by
  by_cases hb : B v <;> simp [cnt, hb]

theorem cnt_upto (u : Nat) (P : List Nat) (N : Nat) {v : Nat} (hv : v < u) :
    ∀ X, cnt (((List.range X).filter (isPt u P N)).map (blockAt u P N)) v =
      below X (fun j => (N + 1 + j) % pr P v == 0)
  | 0 => by simp [cnt, below_zero]
  | X + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, cnt_append, cnt_upto u P N hv X,
      below_succ]
    congr 1
    by_cases hd : (N + 1 + X) % pr P v = 0
    · have hpt : isPt u P N X = true := by
        simp only [isPt, List.any_eq_true, List.mem_range, beq_iff_eq]
        exact ⟨v, hv, hd⟩
      have hbl : blockAt u P N X v = true := by simp [blockAt, hv, hd]
      simp [hpt, cnt_single, hbl, hd]
    · have hbl : blockAt u P N X v = false := by simp [blockAt, hd]
      have hd' : ((N + 1 + X) % pr P v == 0) = false := by simp [hd]
      rw [hd']
      by_cases hpt : isPt u P N X = true
      · simp [hpt, cnt_single, hbl]
      · simp only [Bool.not_eq_true] at hpt
        simp [hpt, cnt]

theorem take_filter_range (f : Nat → Bool) : ∀ (W i : Nat), i < ((List.range W).filter f).length →
    ((List.range W).filter f).take i = (List.range (((List.range W).filter f).getD i 0)).filter f
  | 0, i, hi => by simp at hi
  | W + 1, i, hi => by
    have e : (List.range (W + 1)).filter f = (List.range W).filter f ++ (if f W then [W] else []) := by
      rw [List.range_succ, List.filter_append]
      by_cases hW : f W <;> simp [hW]
    rw [e] at hi ⊢
    by_cases hlt : i < ((List.range W).filter f).length
    · rw [List.take_append_of_le_length (by omega)]
      have hg : ((List.range W).filter f ++ (if f W then [W] else [])).getD i 0 =
          ((List.range W).filter f).getD i 0 := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left hlt]
      rw [hg]
      exact take_filter_range f W i hlt
    · by_cases hW : f W = true
      · simp only [hW, if_true, List.length_append, List.length_cons, List.length_nil] at hi
        have hi' : i = ((List.range W).filter f).length := by omega
        simp only [hW, if_true]
        rw [List.take_left' hi'.symm]
        have hg : ((List.range W).filter f ++ [W]).getD i 0 = W := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hi']
        rw [hg]
      · simp only [Bool.not_eq_true] at hW
        simp only [hW, Bool.false_eq_true, if_false, List.append_nil] at hi
        omega

section
variable {u h : Nat} {P : List Nat} {N W : Nat}

theorem pts_pairwise : (pts u P N W).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem pts_getD_mem {i : Nat} (hi : i < (pts u P N W).length) :
    (pts u P N W).getD i 0 ∈ pts u P N W := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem pts_lt {i : Nat} (hi : i < (pts u P N W).length) : (pts u P N W).getD i 0 < W := by
  have := pts_getD_mem hi
  simp only [pts, List.mem_filter, List.mem_range] at this
  exact this.1

theorem pts_isPt {i : Nat} (hi : i < (pts u P N W).length) :
    isPt u P N ((pts u P N W).getD i 0) = true := by
  have := pts_getD_mem hi
  simp only [pts, List.mem_filter] at this
  exact this.2

theorem pts_mono {i k : Nat} (hik : i < k) (hk : k < (pts u P N W).length) :
    (pts u P N W).getD i 0 < (pts u P N W).getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem (show i < (pts u P N W).length by omega), Option.getD_some]
  exact List.pairwise_iff_getElem.mp pts_pairwise i k _ _ hik

theorem blocks_length : (blocks u P N W).length = (pts u P N W).length := by
  simp [blocks]

theorem blk_blocks {i : Nat} (hi : i < (pts u P N W).length) :
    blk (blocks u P N W) i = blockAt u P N ((pts u P N W).getD i 0) := by
  simp [blk, blocks, List.getElem?_map, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD]

theorem cnt_take {i v : Nat} (hv : v < u) (hi : i < (pts u P N W).length) :
    cnt ((blocks u P N W).take i) v =
      below ((pts u P N W).getD i 0) (fun j => (N + 1 + j) % pr P v == 0) := by
  have e : (blocks u P N W).take i = ((pts u P N W).take i).map (blockAt u P N) := by
    simp [blocks, List.map_take]
  rw [e]
  unfold pts at hi ⊢
  rw [take_filter_range _ W i hi]
  exact cnt_upto u P N hv _

theorem cnt_all {v : Nat} (hv : v < u) :
    cnt (blocks u P N W) v = below W (fun j => (N + 1 + j) % pr P v == 0) :=
  cnt_upto u P N hv W

end

/-! ### The reduction -/

section
variable {u h : Nat} {P : List Nat} {N W : Nat} (hs : Setup u h P N W)
include hs

theorem Setup.linear : Linear u (blocks u P N W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi a ha
    rw [blocks_length] at hi
    rw [blk_blocks hi] at ha
    simp only [blockAt, Bool.and_eq_true, decide_eq_true_eq] at ha
    exact ha.1
  · intro i hi
    rw [blocks_length] at hi
    have hpt := pts_isPt hi
    simp only [isPt, List.any_eq_true, List.mem_range] at hpt
    obtain ⟨v, hv, hdv⟩ := hpt
    have h1 : 1 ≤ below u (fun v => (N + 1 + (pts u P N W).getD i 0) % pr P v == 0) :=
      below_pos hv hdv
    have h2 := hs.good_idx (pts_lt hi)
    obtain ⟨a, b, hab, ha, hb, hfa, hfb⟩ := two_of_below (X := u)
      (f := fun v => (N + 1 + (pts u P N W).getD i 0) % pr P v == 0) (by omega)
    refine ⟨a, b, hab, ?_, ?_⟩ <;> rw [blk_blocks hi] <;>
      simp only [blockAt, Bool.and_eq_true, decide_eq_true_eq]
    · exact ⟨ha, hfa⟩
    · exact ⟨hb, hfb⟩
  · intro j k hj hk hjk a b hab hja hjb hka hkb
    rw [blocks_length] at hj hk
    rw [blk_blocks hj] at hja hjb
    rw [blk_blocks hk] at hka hkb
    simp only [blockAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hja hjb hka hkb
    rcases Nat.lt_or_gt_of_ne hjk with h | h
    · exact hs.sep hab hja.1 hjb.1 (pts_mono h hk) (pts_lt hk) hja.2 hjb.2 hka.2 hkb.2
    · exact hs.sep hab hja.1 hjb.1 (pts_mono h hj) (pts_lt hj) hka.2 hkb.2 hja.2 hjb.2

/-- The first multiple at or after position `X`. -/
theorem Setup.ge {v : Nat} (hv : v < u) (X : Nat) :
    X ≤ first (N + 1) (pr P v) + below X (fun j => (N + 1 + j) % pr P v == 0) * pr P v := by
  rw [below_dvd_eq _ _ _ (hs.pr_pos hv)]
  exact (next_hit _ _ (hs.pr_pos hv) (first_lt _ _ (hs.pr_pos hv)) X).1

theorem Setup.hit {v : Nat} (hv : v < u) {X : Nat} (hX : (N + 1 + X) % pr P v = 0) :
    first (N + 1) (pr P v) + below X (fun j => (N + 1 + j) % pr P v == 0) * pr P v = X := by
  rw [below_dvd_eq _ _ _ (hs.pr_pos hv)]
  exact hit_eq _ _ _ (hs.pr_pos hv) (first_lt _ _ (hs.pr_pos hv))
    ((add_mod_eq_zero_iff _ _ _ (hs.pr_pos hv)).mp hX)

theorem Setup.miss {v : Nat} (hv : v < u) {X : Nat} (hX : (N + 1 + X) % pr P v ≠ 0) :
    X + 1 ≤ first (N + 1) (pr P v) + below X (fun j => (N + 1 + j) % pr P v == 0) * pr P v := by
  rw [below_dvd_eq _ _ _ (hs.pr_pos hv)]
  exact miss_ge _ _ _ (hs.pr_pos hv) (first_lt _ _ (hs.pr_pos hv))
    (fun h => hX ((add_mod_eq_zero_iff _ _ _ (hs.pr_pos hv)).mpr h))

theorem Setup.deg_le {v : Nat} (hv : v < u) : cnt (blocks u P N W) v + 1 ≤ u := by
  have h1 := cnt_le_unmet u (blocks u P N W) hs.linear v (blocks u P N W).length 0 (by omega)
  have h2 : cnt ((blocks u P N W).take 0) v = 0 := by simp [cnt]
  have h3 : unmetIn (blocks u P N W) u 0 v = u - 1 := by
    have e : unmetIn (blocks u P N W) u 0 v = below u (fun w => w != v) := by
      unfold unmetIn below
      congr 1
      apply List.filter_congr
      intro w _
      simp [metIn]
    rw [e, below_ne, if_pos hv]
  omega

theorem Setup.deg_ge {v : Nat} (hv : v < u) : h ≤ cnt (blocks u P N W) v := by
  rw [cnt_all hv]
  have h1 := hs.ge hv W
  have h2 := first_lt (N + 1) (pr P v) (hs.pr_pos hv)
  have h3 : h * pr P v ≤ h * pr P (u - 1) := Nat.mul_le_mul_left _ (hs.pr_le (by omega) (by have := hs.two; omega))
  have h4 := hs.long
  have h5 : h * pr P v < (below W (fun j => (N + 1 + j) % pr P v == 0) + 1) * pr P v := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have := Nat.lt_of_mul_lt_mul_right h5
  omega

theorem Setup.admissible : Admissible u h (blocks u P N W) :=
  { hs.linear with deg := fun _ hv => ⟨hs.deg_ge hv, hs.deg_le hv⟩ }

/-- The smallest prime is at least three. -/
theorem Setup.three : 3 ≤ pr P 0 := by
  have hu := hs.two
  have h2 := (hs.pr_prime (v := 0) (by omega)).1
  apply Nat.lt_of_not_le
  intro hle
  have e : pr P 0 = 2 := by omega
  have h1 := hs.ge (v := 0) (by omega) W
  have hf := first_lt (N + 1) (pr P 0) (hs.pr_pos (by omega))
  have hd := hs.deg_le (v := 0) (by omega)
  rw [cnt_all (by omega)] at hd
  generalize below W (fun j => (N + 1 + j) % pr P 0 == 0) = c at h1 hd
  rw [e] at h1 hf
  have h3 : 2 * pr P 1 ≤ h * pr P (u - 1) :=
    Nat.mul_le_mul hs.hh (hs.pr_le (by omega) (by omega))
  have := hs.long
  have := hs.big
  omega

/-- The integer solution of the sweep system. -/
theorem Setup.system : System u h (blocks u P N W) (fun v => (pr P v : Int))
    (fun v => (first (N + 1) (pr P v) : Int)) (fun i => ((pts u P N W).getD i 0 : Int)) W := by
  have hu := hs.two
  have h3 := hs.three
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast h3
  · intro v hv
    have hlt := hs.pr_lt (show v < v + 1 by omega) hv
    have o1 := hs.odd (v := v) (by omega) h3
    have o2 := hs.odd (v := v + 1) hv h3
    have : pr P v + 2 ≤ pr P (v + 1) := by omega
    exact_mod_cast this
  · have := hs.big
    omega
  · intro v _; omega
  · intro v hv
    have := first_lt (N + 1) (pr P v) (hs.pr_pos hv)
    omega
  · intro v hv
    have h1 := hs.ge hv W
    have h2 := hs.deg_le hv
    rw [cnt_all hv] at h2
    have h4 : below W (fun j => (N + 1 + j) % pr P v == 0) * pr P v ≤ (u - 1) * pr P v :=
      Nat.mul_le_mul_right _ (by omega)
    have h5 : W ≤ first (N + 1) (pr P v) + (u - 1) * pr P v := by omega
    have e : ((u - 1 : Nat) : Int) = (u : Int) - 1 := by omega
    rw [← e]
    exact_mod_cast h5
  · exact_mod_cast hs.long
  · intro _; omega
  · intro i hi
    rw [blocks_length] at hi
    have := pts_mono (show i < i + 1 by omega) hi
    omega
  · intro i hi
    rw [blocks_length] at hi
    have := pts_lt hi
    omega
  · intro i hi v hv hb
    rw [blocks_length] at hi
    rw [blk_blocks hi] at hb
    simp only [blockAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
    rw [cnt_take hv hi]
    exact_mod_cast hs.hit hv hb.2
  · intro i hi v hv hb
    rw [blocks_length] at hi
    rw [blk_blocks hi] at hb
    rw [cnt_take hv hi]
    generalize (pts u P N W).getD i 0 = x at hb ⊢
    have hd : (N + 1 + x) % pr P v ≠ 0 := by
      intro h0; simp [blockAt, hv, h0] at hb
    exact_mod_cast hs.miss hv hd
  · intro v hv
    rw [cnt_all hv]
    exact_mod_cast hs.ge hv W

theorem Setup.parity : ParityOK (blocks u P N W) (fun v => (first (N + 1) (pr P v) : Int)) := by
  intro i hi v w hbv hbw
  dsimp only
  have h3 := hs.three
  rw [blocks_length] at hi
  rw [blk_blocks hi] at hbv hbw
  simp only [blockAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbv hbw
  rw [cnt_take hbv.1 hi, cnt_take hbw.1 hi]
  have e1 := hs.hit hbv.1 hbv.2
  have e2 := hs.hit hbw.1 hbw.2
  have o1 := hs.odd hbv.1 h3
  have o2 := hs.odd hbw.1 h3
  generalize below ((pts u P N W).getD i 0) (fun j => (N + 1 + j) % pr P v == 0) = cv at e1 ⊢
  generalize below ((pts u P N W).getD i 0) (fun j => (N + 1 + j) % pr P w == 0) = cw at e2 ⊢
  have m1 : cv * pr P v % 2 = cv % 2 := by rw [Nat.mul_mod, o1]; simp
  have m2 : cw * pr P w % 2 = cw % 2 := by rw [Nat.mul_mod, o2]; simp
  generalize cv * pr P v = a at e1 m1
  generalize cw * pr P w = b at e2 m2
  omega

end

end SweepCheck
