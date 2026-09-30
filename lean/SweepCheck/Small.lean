/-
Sets of primes with a small second prime.

For these sets the separation lemma is not available.  Instead the counting inequality of the run
lemma leaves only finitely many sets, which `enumOK` lists by a search over the primes in
increasing order, and for each of them `leafOK` shows by a search over the residues of the
interval's start that no interval of the required length is good.
-/
import SweepCheck.Interval

namespace SweepCheck

/-! ### Sums over lists -/

theorem sum_append' (l₁ l₂ : List Nat) : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, List.sum_cons, ih]; omega

theorem sum_map_add (L : List Nat) (f g : Nat → Nat) :
    (L.map (fun q => f q + g q)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => rfl
  | cons q L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_mul_left (L : List Nat) (a : Nat) (f : Nat → Nat) :
    (L.map (fun q => a * f q)).sum = a * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons q L ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_map_mul_right (L : List Nat) (a : Nat) (f : Nat → Nat) :
    (L.map (fun q => f q * a)).sum = (L.map f).sum * a := by
  induction L with
  | nil => simp
  | cons q L ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem sum_map_const (L : List Nat) (a : Nat) : (L.map (fun _ => a)).sum = L.length * a := by
  induction L with
  | nil => simp
  | cons q L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.add_mul]; omega

/-! ### The search over residues -/

/-- The number of `j < L` lying in exactly one of the residue classes `j ≡ s (mod q)`,
`(q, s) ∈ asg`. -/
def lone (L : Nat) (asg : List (Nat × Nat)) : Nat :=
  below L (fun j => asg.countP (fun e => j % e.1 == e.2) == 1)

/-- True when every choice of residues `s < q` for the moduli `q` of `rest`, added to the choices
in `asg`, leaves some `j < L` in exactly one class.  A branch is cut when more such `j` exist than
the remaining classes can reach. -/
def leafOK (L : Nat) (asg : List (Nat × Nat)) : List Nat → Bool
  | [] => decide (0 < lone L asg)
  | q :: rest => decide (((q :: rest).map (fun r => (L + r - 1) / r)).sum < lone L asg) ||
      (List.range q).all (fun s => leafOK L ((q, s) :: asg) rest)

theorem lone_map (L : Nat) (o : Nat → Nat) (A : List Nat) :
    lone L (A.map (fun q => (q, o q))) = below L (fun j => A.countP (fun q => j % q == o q) == 1) := by
  unfold lone
  apply below_congr
  intro j _
  rw [List.countP_map]
  rfl

/-- If the residues `o q` make every `j < L` lie in a number of classes other than one, the
search does not succeed. -/
theorem leafOK_false (L : Nat) (o : Nat → Nat) (ho : ∀ q, 0 < q → o q < q) :
    ∀ (rest A : List Nat), (∀ q ∈ rest, 0 < q) →
      (∀ j < L, (A ++ rest).countP (fun q => j % q == o q) ≠ 1) →
      leafOK L (A.map (fun q => (q, o q))) rest = false := by
  intro rest
  induction rest with
  | nil =>
    intro A _ hgood
    simp only [leafOK, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero, lone_map]
    have := below_mono L (f := fun j => A.countP (fun q => j % q == o q) == 1)
      (g := fun _ => false) (fun j hj h1 => by
        have := hgood j hj
        simp only [List.append_nil] at this
        simp only [beq_iff_eq] at h1
        exact absurd h1 this)
    have h0 : below L (fun _ => false) = 0 := by simp [below]
    omega
  | cons q rest ih =>
    intro A hpos hgood
    simp only [leafOK, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]
    constructor
    · -- the singular `j` are reached by the remaining classes
      rw [lone_map]
      let sing : Nat → Bool := fun j => A.countP (fun q => j % q == o q) == 1
      have hcov : ∀ j ∈ (List.range L).filter sing, ∃ r ∈ q :: rest, (j % r == o r) = true := by
        intro j hj
        rw [List.mem_filter, List.mem_range] at hj
        have h1 := hgood j hj.1
        have h2 : A.countP (fun q => j % q == o q) = 1 := by simpa [sing] using hj.2
        rw [List.countP_append, h2] at h1
        have : 0 < (q :: rest).countP (fun q => j % q == o q) := by omega
        exact List.countP_pos_iff.mp this
      have hl := length_le_sum (q :: rest) (fun r j => j % r == o r) _ hcov
      dsimp only at hl
      have hle : ((q :: rest).map (fun r => (((List.range L).filter sing).filter
          (fun j => j % r == o r)).length)).sum ≤ ((q :: rest).map (fun r => (L + r - 1) / r)).sum := by
        apply sum_map_le
        intro r hr
        have hr0 := hpos r hr
        have h1 : (((List.range L).filter sing).filter (fun j => j % r == o r)).length ≤
            below L (fun j => j % r == o r) :=
          (List.Sublist.filter _ List.filter_sublist).length_le
        have h2 := below_mod_le r (o r) L hr0
        have h3 : below L (fun j => j % r == o r) ≤ (L + r - 1) / r :=
          (Nat.le_div_iff_mul_le hr0).mpr h2
        omega
      show below L sing ≤ _
      unfold below
      omega
    · -- the branch with the residue `o q` fails
      rw [List.all_eq_false]
      refine ⟨o q, List.mem_range.mpr (ho q (hpos q List.mem_cons_self)), ?_⟩
      have := ih (q :: A) (fun r hr => hpos r (List.mem_cons_of_mem _ hr)) (by
        intro j hj
        have := hgood j hj
        simp only [List.countP_append, List.countP_cons] at this ⊢
        omega)
      simp only [List.map_cons] at this
      simp [this]

/-! ### The search over sets of primes -/

/-- The product of a list. -/
def prodL : List Nat → Nat
  | [] => 1
  | q :: Q => q * prodL Q

theorem dvd_prodL {q : Nat} : ∀ {Q : List Nat}, q ∈ Q → q ∣ prodL Q
  | [], h => by simp at h
  | r :: Q, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (dvd_prodL h) (Nat.dvd_mul_left _ _)

theorem prodL_pos : ∀ {Q : List Nat}, (∀ q ∈ Q, 0 < q) → 0 < prodL Q
  | [], _ => by simp [prodL]
  | r :: Q, h => Nat.mul_pos (h r List.mem_cons_self)
      (prodL_pos (fun q hq => h q (List.mem_cons_of_mem _ hq)))

/-- Every completion of `p₁ :: Qf` by numbers that are at least `c`, up to `u` elements in all,
violates the counting inequality of the run lemma. -/
def cut (u h p1 : Nat) (Qf : List Nat) (c : Nat) : Bool :=
  let D := prodL Qf * c
  let A := (Qf.map (fun q => D / q)).sum + (u - 1 - Qf.length) * (D / c)
  decide (A < D) && decide ((u - 2) * D < (h * c / p1 - 1) * (D - A))

theorem cut_sound (u h p1 : Nat) (hu : 2 ≤ u) (Qf R : List Nat) (c : Nat) (hc : 0 < c)
    (hQf : ∀ q ∈ Qf, 0 < q) (hR : ∀ r ∈ R, c ≤ r) (hlen : Qf.length + R.length = u - 1)
    (K M : Nat) (hM : c ≤ M) (hK : K = h * M / p1) (b : Nat → Nat)
    (hb : ∀ q ∈ Qf ++ R, b q * q ≤ K + q - 1) (hsum : K ≤ ((Qf ++ R).map b).sum)
    (hcut : cut u h p1 Qf c = true) : False := by
  simp only [cut, Bool.and_eq_true, decide_eq_true_eq] at hcut
  obtain ⟨hAD, hmain⟩ := hcut
  -- notation
  generalize hD : prodL Qf * c = D at hAD hmain
  have hDpos : 0 < D := by rw [← hD]; exact Nat.mul_pos (prodL_pos hQf) hc
  have hcD : c ∣ D := by rw [← hD]; exact Nat.dvd_mul_left _ _
  have hqD : ∀ q ∈ Qf, q ∣ D := fun q hq => by
    rw [← hD]; exact Nat.dvd_trans (dvd_prodL hq) (Nat.dvd_mul_right _ _)
  -- the bound for the fixed elements
  have hfix : ∀ q ∈ Qf, b q * D ≤ (K - 1) * (D / q) + D := by
    intro q hq
    have hq0 := hQf q hq
    have e : D = q * (D / q) := (Nat.mul_div_cancel' (hqD q hq)).symm
    have h1 := hb q (List.mem_append_left _ hq)
    have h2 : b q * q * (D / q) ≤ (K - 1 + q) * (D / q) := Nat.mul_le_mul_right _ (by omega)
    calc b q * D = b q * q * (D / q) := by rw [Nat.mul_assoc, ← e]
      _ ≤ (K - 1 + q) * (D / q) := h2
      _ = (K - 1) * (D / q) + D := by rw [Nat.add_mul, ← e]
  -- the bound for the new elements
  have hnew : ∀ r ∈ R, b r * D ≤ (K - 1) * (D / c) + D := by
    intro r hr
    have hcr := hR r hr
    have e : D = c * (D / c) := (Nat.mul_div_cancel' hcD).symm
    have h1 := hb r (List.mem_append_right _ hr)
    have h2 : b r * c ≤ K - 1 + c := by
      cases hbr : b r with
      | zero => simp
      | succ k =>
        rw [hbr] at h1
        have h3 : k * r + r ≤ K + r - 1 := by rw [Nat.succ_mul] at h1; exact h1
        have h4 : k * c ≤ k * r := Nat.mul_le_mul_left _ hcr
        rw [Nat.succ_mul]
        omega
    calc b r * D = b r * c * (D / c) := by rw [Nat.mul_assoc, ← e]
      _ ≤ (K - 1 + c) * (D / c) := Nat.mul_le_mul_right _ h2
      _ = (K - 1) * (D / c) + D := by rw [Nat.add_mul, ← e]
  -- summing up
  generalize hS : (Qf.map (fun q => D / q)).sum = S at hAD hmain
  generalize hA : S + (u - 1 - Qf.length) * (D / c) = A at hAD hmain
  have hs1 : K * D ≤ ((Qf ++ R).map (fun q => b q * D)).sum := by
    rw [sum_map_mul_right]; exact Nat.mul_le_mul_right _ hsum
  have hs2 : ((Qf ++ R).map (fun q => b q * D)).sum ≤
      ((K - 1) * S + Qf.length * D) + R.length * ((K - 1) * (D / c) + D) := by
    rw [List.map_append, sum_append']
    apply Nat.add_le_add
    · calc (Qf.map (fun q => b q * D)).sum ≤ (Qf.map (fun q => (K - 1) * (D / q) + D)).sum :=
            sum_map_le _ _ _ hfix
        _ = (K - 1) * S + Qf.length * D := by rw [sum_map_add, sum_map_mul_left, sum_map_const, hS]
    · calc (R.map (fun q => b q * D)).sum ≤ (R.map (fun _ => (K - 1) * (D / c) + D)).sum :=
            sum_map_le _ _ _ hnew
        _ = R.length * ((K - 1) * (D / c) + D) := sum_map_const _ _
  have hRlen : R.length = u - 1 - Qf.length := by omega
  rw [hRlen, Nat.mul_add] at hs2
  have eA : (K - 1) * A = (K - 1) * S + (u - 1 - Qf.length) * ((K - 1) * (D / c)) := by
    rw [← hA, Nat.mul_add, Nat.mul_left_comm]
  have eD : Qf.length * D + (u - 1 - Qf.length) * D = (u - 1) * D := by
    rw [← Nat.add_mul]; congr 1; omega
  have hKA : K * D ≤ (K - 1) * A + (u - 1) * D := by omega
  -- a lower bound for `K`
  have hK0 : h * c / p1 ≤ K := by rw [hK]; exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hM)
  have hK1 : (h * c / p1 - 1) * (D - A) ≤ (K - 1) * (D - A) := Nat.mul_le_mul_right _ (by omega)
  have hK2 : (K - 1) * (D - A) ≤ (u - 2) * D := by
    cases hk : K with
    | zero => simp
    | succ k =>
      rw [hk] at hKA
      rw [Nat.add_sub_cancel, Nat.mul_sub]
      rw [Nat.succ_mul, Nat.add_sub_cancel] at hKA
      have e3 : (u - 1) * D = (u - 2) * D + D := by
        rw [← Nat.succ_mul]; congr 1; omega
      have e4 : k * A ≤ k * D := Nat.mul_le_mul_left _ (by omega)
      omega
  omega

/-- The last element of a list (zero for the empty list). -/
def lastD : List Nat → Nat
  | [] => 0
  | [a] => a
  | _ :: b :: l => lastD (b :: l)

theorem lastD_append (l R : List Nat) (hR : R ≠ []) : lastD (l ++ R) = lastD R := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil =>
      cases R with
      | nil => exact absurd rfl hR
      | cons b R => rfl
    | cons b l => exact ih

theorem lastD_mem : ∀ {l : List Nat}, l ≠ [] → lastD l ∈ l
  | [], h => absurd rfl h
  | [a], _ => by simp [lastD]
  | a :: b :: l, _ => List.mem_cons_of_mem _ (lastD_mem (l := b :: l) (by simp))

theorem le_lastD : ∀ {l : List Nat}, l.Pairwise (· < ·) → ∀ x ∈ l, x ≤ lastD l
  | [], _, x, hx => by simp at hx
  | [a], _, x, hx => by simp at hx; simp [lastD, hx]
  | a :: b :: l, hs, x, hx => by
    have ih := le_lastD (l := b :: l) (List.Pairwise.of_cons hs)
    rcases List.mem_cons.mp hx with h | h
    · subst h
      have h1 : x < lastD (b :: l) :=
        List.rel_of_pairwise_cons hs (lastD_mem (l := b :: l) (by simp))
      exact Nat.le_of_lt h1
    · exact ih x h

/-- The test for a complete set `p₁ :: Q` with largest element `M`: the counting inequality
fails, or no interval of length `h M` is good. -/
def leafTest (h p1 : Nat) (Q : List Nat) (M : Nat) : Bool :=
  decide ((Q.map (fun q => (h * M / p1 + q - 1) / q)).sum < h * M / p1) ||
    leafOK (h * M) [] (p1 :: Q)

/-- The hypothesis to be refuted: `p₁ :: Q` is a sorted list of primes with a good interval of
length `h` times its last element. -/
def HasGood (h p1 : Nat) (Q : List Nat) : Prop :=
  (∀ q ∈ p1 :: Q, IsPrime q) ∧ (p1 :: Q).Pairwise (· < ·) ∧ ∃ N, Good (p1 :: Q) N (h * lastD Q)

theorem counting_of_hasGood {h p1 : Nat} {Q : List Nat} (hg : HasGood h p1 Q) :
    ∃ b : Nat → Nat, (∀ q ∈ Q, b q * q ≤ h * lastD Q / p1 + q - 1) ∧
      h * lastD Q / p1 ≤ (Q.map b).sum := by
  obtain ⟨hp, hs, N, hgood⟩ := hg
  have hK : p1 * (h * lastD Q / p1) ≤ h * lastD Q := Nat.mul_div_le _ _
  refine ⟨fun q => below (h * lastD Q / p1) (fun i => (N / p1 + 1 + i) % q == 0), ?_,
    run_count hp hs hgood hK⟩
  intro q hq
  exact below_dvd_le _ _ _ (hp q (List.mem_cons_of_mem _ hq)).pos

theorem leafTest_sound {h p1 : Nat} {Q : List Nat}
    (hl : leafTest h p1 Q (lastD Q) = true) (hg : HasGood h p1 Q) : False := by
  simp only [leafTest, Bool.or_eq_true, decide_eq_true_eq] at hl
  rcases hl with hl | hl
  · obtain ⟨b, hb, hsum⟩ := counting_of_hasGood hg
    have hp := hg.1
    have : (Q.map b).sum ≤ (Q.map (fun q => (h * lastD Q / p1 + q - 1) / q)).sum := by
      apply sum_map_le
      intro q hq
      have hq0 := (hp q (List.mem_cons_of_mem _ hq)).pos
      exact (Nat.le_div_iff_mul_le hq0).mpr (hb q hq)
    omega
  · obtain ⟨hp, _, N, hgood⟩ := hg
    have := leafOK_false (h * lastD Q) (fun q => first (N + 1) q)
      (fun q hq => first_lt _ _ hq) (p1 :: Q) [] (fun q hq => (hp q hq).pos) (by
        intro j hj
        have := hgood (N + 1 + j) (by omega) (by omega)
        rw [List.nil_append]
        rwa [List.countP_congr (q := fun q => (N + 1 + j) % q == 0)]
        intro q hq
        simp only [beq_iff_eq]
        exact (add_mod_eq_zero_iff (N + 1) q j (hp q hq).pos).symm)
    have h2 : leafOK (h * lastD Q) [] (p1 :: Q) = false := this
    rw [h2] at hl
    exact Bool.false_ne_true hl

/-- The search over the elements after `p₁ :: Qf`, trying `c, c + 1, …` for the next one. -/
def enumOK (u h p1 : Nat) : Nat → List Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, Qf, c =>
    cut u h p1 Qf c ||
      ((!isPrimeB c ||
          (if Qf.length + 2 = u then leafTest h p1 (Qf ++ [c]) c
           else enumOK u h p1 fuel (Qf ++ [c]) (c + 1))) &&
        enumOK u h p1 fuel Qf (c + 1))

theorem enumOK_sound (u h p1 : Nat) :
    ∀ fuel Qf c, enumOK u h p1 fuel Qf c = true → 0 < c → (∀ q ∈ Qf, 0 < q) →
      ∀ R : List Nat, R ≠ [] → Qf.length + R.length = u - 1 → (∀ r ∈ R, c ≤ r) →
        ¬ HasGood h p1 (Qf ++ R)
  | 0, _, _, he, _, _, _, _, _, _ => by simp [enumOK] at he
  | fuel + 1, Qf, c, he, hc, hQf, R, hR, hlen, hRc => by
    intro hg
    simp only [enumOK, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at he
    rcases he with hcut | ⟨hstep, hrest⟩
    · -- the cut applies
      obtain ⟨b, hb, hsum⟩ := counting_of_hasGood hg
      have hM : c ≤ lastD (Qf ++ R) := by
        rw [lastD_append _ _ hR]; exact hRc _ (lastD_mem hR)
      have hu : 2 ≤ u := by
        have : R.length ≠ 0 := fun h0 => hR (List.eq_nil_of_length_eq_zero h0)
        omega
      exact cut_sound u h p1 hu Qf R c hc hQf hRc hlen _ _ hM rfl b hb hsum hcut
    · obtain ⟨r, R', rfl⟩ : ∃ r R', R = r :: R' := by
        cases R with
        | nil => exact absurd rfl hR
        | cons r R' => exact ⟨r, R', rfl⟩
      have hp := hg.1
      have hs := hg.2.1
      have hsR : (r :: R').Pairwise (· < ·) := by
        have := List.Pairwise.of_cons hs
        exact List.pairwise_append.mp this |>.2.1
      have hR'r : ∀ x ∈ R', r < x := fun x hx => List.rel_of_pairwise_cons hsR hx
      by_cases hrc : r = c
      · subst hrc
        have hprime : isPrimeB r = true :=
          isPrimeB_of_isPrime (hp r (by simp))
        rw [hprime] at hstep
        replace hstep : (if Qf.length + 2 = u then leafTest h p1 (Qf ++ [r]) r
            else enumOK u h p1 fuel (Qf ++ [r]) (r + 1)) = true := by
          rcases hstep with h0 | h0
          · exact absurd h0 (by decide)
          · exact h0
        by_cases hu : Qf.length + 2 = u
        · rw [if_pos hu] at hstep
          have hR' : R' = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_cons] at hlen
            omega
          subst hR'
          exact leafTest_sound (by rw [lastD_append _ _ (by simp)]; exact hstep) hg
        · rw [if_neg hu] at hstep
          have hR'ne : R' ≠ [] := by
            intro h0; subst h0
            simp only [List.length_cons, List.length_nil] at hlen
            omega
          have := enumOK_sound u h p1 fuel (Qf ++ [r]) (r + 1) hstep (by omega)
            (by
              intro q hq
              rcases List.mem_append.mp hq with h1 | h1
              · exact hQf q h1
              · simp at h1; omega)
            R' hR'ne (by
              have e1 : (Qf ++ [r]).length = Qf.length + 1 := by simp
              have e2 : (r :: R').length = R'.length + 1 := rfl
              omega)
            (fun x hx => hR'r x hx)
          apply this
          simpa using hg
      · have hcr : c < r := by have := hRc r List.mem_cons_self; omega
        exact enumOK_sound u h p1 fuel Qf (c + 1) hrest (by omega) hQf (r :: R') hR hlen
          (by
            intro x hx
            rcases List.mem_cons.mp hx with h1 | h1
            · omega
            · have := hR'r x h1; omega) hg

/-- The whole search for one pair `(u, h)`: every pair of primes `p₁ < p₂ ≤ 2u - 3`. -/
def smallOK (u h : Nat) : Bool :=
  (List.range (2 * u - 2)).all (fun p2 =>
    !isPrimeB p2 || (List.range p2).all (fun p1 => !isPrimeB p1 || enumOK u h p1 100000 [p2] (p2 + 1)))

theorem smallOK_sound (u h : Nat) (hok : smallOK u h = true) (hu : 3 ≤ u) (p1 p2 : Nat) (R : List Nat)
    (hlen : R.length + 2 = u) (hp : ∀ q ∈ p1 :: p2 :: R, IsPrime q)
    (hs : (p1 :: p2 :: R).Pairwise (· < ·)) (hsmall : p2 ≤ 2 * u - 3) (N W : Nat)
    (hg : Good (p1 :: p2 :: R) N W) : W < h * lastD (p2 :: R) := by
  apply Nat.lt_of_not_le
  intro hW
  have hR : R ≠ [] := by intro h0; subst h0; simp at hlen; omega
  have h12 : p1 < p2 := List.rel_of_pairwise_cons hs (by simp)
  have hpr2 := isPrimeB_of_isPrime (hp p2 (by simp))
  have hpr1 := isPrimeB_of_isPrime (hp p1 (by simp))
  simp only [smallOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hok
  rcases hok p2 (by omega) with h0 | h0
  · rw [hpr2] at h0; exact Bool.false_ne_true h0.symm
  rcases h0 p1 h12 with h1 | h1
  · rw [hpr1] at h1; exact Bool.false_ne_true h1.symm
  have hs2 : (p2 :: R).Pairwise (· < ·) := List.Pairwise.of_cons hs
  refine enumOK_sound u h p1 100000 [p2] (p2 + 1) h1 (by omega)
    (by intro q hq; simp at hq; rw [hq]; exact (hp p2 (by simp)).pos)
    R hR (by simp; omega) (fun r hr => List.rel_of_pairwise_cons hs2 hr) ⟨hp, hs, N, ?_⟩
  exact hg.mono (by simpa using hW)

end SweepCheck
