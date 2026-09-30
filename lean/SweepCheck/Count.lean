/-
Counting multiples in a run of consecutive integers.

`below X f` is the number of `j < X` with `f j`.  The main facts are that the numbers `a + j`
divisible by `p` are those with `j` in one residue class `f` modulo `p`, that the first `j ≥ X`
in this class is `f + (below X ·) * p`, and the resulting bound on the number of multiples of `p`
among `K` consecutive integers.  A union bound turns these into the counting argument of the paper.
-/

namespace SweepCheck

/-- The number of `j < X` with `f j`. -/
def below (X : Nat) (f : Nat → Bool) : Nat := ((List.range X).filter f).length

theorem below_zero (f : Nat → Bool) : below 0 f = 0 := rfl

theorem below_succ (X : Nat) (f : Nat → Bool) :
    below (X + 1) f = below X f + (if f X then 1 else 0) := by
  unfold below
  rw [List.range_succ, List.filter_append]
  by_cases h : f X <;> simp [h]

theorem below_congr (X : Nat) {f g : Nat → Bool} (h : ∀ j, j < X → f j = g j) :
    below X f = below X g := by
  unfold below
  congr 1
  apply List.filter_congr
  intro j hj
  exact h j (List.mem_range.mp hj)

theorem below_mono (X : Nat) {f g : Nat → Bool} (h : ∀ j, j < X → f j = true → g j = true) :
    below X f ≤ below X g := by
  induction X with
  | zero => simp [below_zero]
  | succ X ih =>
    rw [below_succ, below_succ]
    have := ih (fun j hj => h j (by omega))
    by_cases hf : f X = true
    · have hg := h X (by omega) hf
      simp [hf, hg]; omega
    · rw [if_neg hf]
      split <;> omega

theorem below_le (X : Nat) (f : Nat → Bool) : below X f ≤ X := by
  induction X with
  | zero => simp [below_zero]
  | succ X ih => rw [below_succ]; split <;> omega

/-- The numbers `a + j` divisible by `p` are those with `j ≡ first a p` modulo `p`. -/
def first (a p : Nat) : Nat := (p - a % p) % p

theorem first_lt (a p : Nat) (hp : 0 < p) : first a p < p := Nat.mod_lt _ hp

theorem add_mod_eq_zero_iff (a p j : Nat) (hp : 0 < p) :
    (a + j) % p = 0 ↔ j % p = first a p := by
  have ha := Nat.mod_lt a hp
  have hj := Nat.mod_lt j hp
  rw [Nat.add_mod]
  unfold first
  by_cases h0 : a % p = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  · have e1 : (p - a % p) % p = p - a % p := Nat.mod_eq_of_lt (by omega)
    rw [e1]
    by_cases hs : a % p + j % p < p
    · rw [Nat.mod_eq_of_lt hs]; omega
    · have e2 : (a % p + j % p) % p = a % p + j % p - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e2]; omega

/-- The first `j ≥ X` with `j ≡ f` modulo `p` is `f + (below X ·) * p`. -/
theorem next_hit (p f : Nat) (hp : 0 < p) (hf : f < p) :
    ∀ X, X ≤ f + below X (fun j => j % p == f) * p ∧
      f + below X (fun j => j % p == f) * p < X + p
  | 0 => by simp [below_zero]; omega
  | X + 1 => by
    obtain ⟨h1, h2⟩ := next_hit p f hp hf X
    rw [below_succ]
    have hmod : (f + below X (fun j => j % p == f) * p) % p = f := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf]
    by_cases hX : X % p = f
    · have hX' : (X % p == f) = true := by simp [hX]
      simp only [hX', if_true]
      -- the hit at or after `X` is `X` itself
      have heq : f + below X (fun j => j % p == f) * p = X := by
        have hd : p ∣ f + below X (fun j => j % p == f) * p - X := by
          apply Nat.dvd_of_mod_eq_zero
          apply Nat.sub_mod_eq_zero_of_mod_eq
          rw [hmod, hX]
        have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
        omega
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · have hX' : (X % p == f) = false := by simp [hX]
      simp only [hX', Bool.false_eq_true, if_false, Nat.add_zero]
      have hne : f + below X (fun j => j % p == f) * p ≠ X := by
        intro h
        rw [h] at hmod
        exact hX hmod
      omega

/-- If `X` lies in the class, the first element of the class at or after `X` is `X`. -/
theorem hit_eq (p f X : Nat) (hp : 0 < p) (hf : f < p) (hX : X % p = f) :
    f + below X (fun j => j % p == f) * p = X := by
  obtain ⟨h1, h2⟩ := next_hit p f hp hf X
  have hmod : (f + below X (fun j => j % p == f) * p) % p = f := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf]
  have hd : p ∣ f + below X (fun j => j % p == f) * p - X := by
    apply Nat.dvd_of_mod_eq_zero
    apply Nat.sub_mod_eq_zero_of_mod_eq
    rw [hmod, hX]
  have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

/-- If `X` is not in the class, the first element of the class after `X` exceeds `X`. -/
theorem miss_ge (p f X : Nat) (hp : 0 < p) (hf : f < p) (hX : X % p ≠ f) :
    X + 1 ≤ f + below X (fun j => j % p == f) * p := by
  obtain ⟨h1, _⟩ := next_hit p f hp hf X
  have hmod : (f + below X (fun j => j % p == f) * p) % p = f := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf]
  have hne : f + below X (fun j => j % p == f) * p ≠ X := by
    intro h
    rw [h] at hmod
    exact hX hmod
  omega

/-- Counting the multiples of `p` among `a, …, a + X - 1` is counting a residue class. -/
theorem below_dvd_eq (a p X : Nat) (hp : 0 < p) :
    below X (fun j => (a + j) % p == 0) = below X (fun j => j % p == first a p) := by
  apply below_congr
  intro j _
  show ((a + j) % p == 0) = (j % p == first a p)
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact add_mod_eq_zero_iff a p j hp

/-- At most `(X + p - 1) / p` of the numbers `j < X` lie in one residue class modulo `p`. -/
theorem below_mod_le (p s X : Nat) (hp : 0 < p) :
    below X (fun j => j % p == s) * p ≤ X + p - 1 := by
  by_cases hs : s < p
  · have := (next_hit p s hp hs X).2
    omega
  · have : below X (fun j => j % p == s) = 0 := by
      have h0 := below_mono X (f := fun j => j % p == s) (g := fun _ => false)
        (fun j _ hj => by
          have := Nat.mod_lt j hp
          simp only [beq_iff_eq] at hj
          omega)
      have : below X (fun _ => false) = 0 := by simp [below]
      omega
    rw [this]; omega

/-- Among `K` consecutive integers `a, …, a + K - 1` at most `(K + p - 1) / p` are divisible by `p`. -/
theorem below_dvd_le (a p K : Nat) (hp : 0 < p) :
    below K (fun j => (a + j) % p == 0) * p ≤ K + p - 1 := by
  rw [below_dvd_eq a p K hp]
  exact below_mod_le p _ K hp

/-- `below` splits along a second test. -/
theorem below_split (X : Nat) (f g : Nat → Bool) :
    below X f = below X (fun j => f j && g j) + below X (fun j => f j && !g j) := by
  induction X with
  | zero => simp [below_zero]
  | succ X ih =>
    rw [below_succ, below_succ, below_succ, ih]
    cases f X <;> cases g X <;> simp <;> omega

theorem below_pos {X : Nat} {f : Nat → Bool} {a : Nat} (ha : a < X) (hf : f a = true) :
    1 ≤ below X f := by
  induction X with
  | zero => omega
  | succ X ih =>
    rw [below_succ]
    by_cases haX : a = X
    · subst haX; simp [hf]
    · have := ih (by omega); omega

theorem exists_of_below_pos {X : Nat} {f : Nat → Bool} (h : 1 ≤ below X f) :
    ∃ a, a < X ∧ f a = true := by
  induction X with
  | zero => simp [below_zero] at h
  | succ X ih =>
    rw [below_succ] at h
    by_cases hX : f X = true
    · exact ⟨X, by omega, hX⟩
    · rw [if_neg hX] at h
      obtain ⟨a, ha, hfa⟩ := ih (by omega)
      exact ⟨a, by omega, hfa⟩

theorem below_eq_le_one (X a : Nat) : below X (fun j => j == a) ≤ 1 := by
  induction X with
  | zero => simp [below_zero]
  | succ X ih =>
    rw [below_succ]
    by_cases hX : X = a
    · subst hX
      have : below X (fun j => j == X) = 0 := by
        have h0 := below_mono X (f := fun j => j == X) (g := fun _ => false)
          (fun j hj hj' => by simp at hj'; omega)
        have : below X (fun _ => false) = 0 := by simp [below]
        omega
      simp [this]
    · simp [hX]; exact ih

/-- Two distinct witnesses when the count is at least two. -/
theorem two_of_below {X : Nat} {f : Nat → Bool} (h : 2 ≤ below X f) :
    ∃ a b, a ≠ b ∧ a < X ∧ b < X ∧ f a = true ∧ f b = true := by
  obtain ⟨a, ha, hfa⟩ := exists_of_below_pos (X := X) (f := f) (by omega)
  have hs := below_split X f (fun j => j != a)
  have h1 : below X (fun j => f j && !(j != a)) ≤ 1 := by
    have := below_mono X (f := fun j => f j && !(j != a)) (g := fun j => j == a)
      (fun j _ hj => by simp at hj; simp [hj.2])
    have := below_eq_le_one X a
    omega
  obtain ⟨b, hb, hfb⟩ := exists_of_below_pos (X := X) (f := fun j => f j && (j != a)) (by omega)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hfb
  exact ⟨a, b, fun e => hfb.2 e.symm, ha, hb, hfa, hfb.1⟩

theorem below_ne (X v : Nat) : below X (fun w => w != v) = if v < X then X - 1 else X := by
  induction X with
  | zero => simp [below_zero]
  | succ X ih =>
    rw [below_succ, ih]
    by_cases h1 : v < X
    · have : (X != v) = true := by simp; omega
      simp only [h1, if_true, this, show v < X + 1 from by omega]
      omega
    · by_cases h2 : v = X
      · subst h2; simp
      · have : (X != v) = true := by simp; omega
        simp only [h1, if_false, this, if_true, show ¬ v < X + 1 from by omega]

theorem sum_map_le (Q : List Nat) (g k : Nat → Nat) (hle : ∀ q ∈ Q, g q ≤ k q) :
    (Q.map g).sum ≤ (Q.map k).sum := by
  induction Q with
  | nil => simp
  | cons q Q ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := hle q List.mem_cons_self
    have h2 := ih (fun q' hq' => hle q' (List.mem_cons_of_mem _ hq'))
    omega

/-- Union bound: if every `j < X` satisfies one of the tests `f q`, `q ∈ Q`, then `X` is at most
the sum over `q` of the number of `j < X` passing `f q`. -/
theorem length_le_sum (Q : List Nat) (f : Nat → Nat → Bool) :
    ∀ (l : List Nat), (∀ a ∈ l, ∃ q ∈ Q, f q a = true) →
      l.length ≤ (Q.map (fun q => (l.filter (f q)).length)).sum := by
  induction Q with
  | nil =>
    intro l hl
    cases l with
    | nil => simp
    | cons a l =>
      obtain ⟨q, hq, _⟩ := hl a (List.mem_cons_self)
      simp at hq
  | cons q Q ih =>
    intro l hl
    have hsplit : l.length = (l.filter (f q)).length + (l.filter (fun a => !f q a)).length := by
      have := List.length_eq_countP_add_countP (f q) (l := l)
      simp only [List.countP_eq_length_filter] at this
      rw [this]
      congr 2
      apply List.filter_congr
      intro a _
      cases f q a <;> rfl
    have hrest := ih (l.filter (fun a => !f q a)) (by
      intro a ha
      rw [List.mem_filter] at ha
      obtain ⟨q', hq', hf⟩ := hl a ha.1
      rcases List.mem_cons.mp hq' with h | h
      · subst h; simp [hf] at ha
      · exact ⟨q', h, hf⟩)
    have hsum : (Q.map (fun q' => ((l.filter (fun a => !f q a)).filter (f q')).length)).sum ≤
        (Q.map (fun q' => (l.filter (f q')).length)).sum := by
      apply sum_map_le
      intro q' _
      exact (List.Sublist.filter (f q') List.filter_sublist).length_le
    simp only [List.map_cons, List.sum_cons]
    omega

end SweepCheck
