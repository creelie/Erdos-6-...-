/-
Elementary facts about block sequences used in the soundness proof.
-/
import SweepCheck.Spec

namespace SweepCheck

theorem cnt_nil (v : Nat) : cnt [] v = 0 := rfl

theorem cnt_append (a b : List (Nat → Bool)) (v : Nat) : cnt (a ++ b) v = cnt a v + cnt b v := by
  simp [cnt, List.filter_append]

theorem cnt_take_succ (bs : List (Nat → Bool)) (i v : Nat) (hi : i < bs.length) :
    cnt (bs.take (i + 1)) v = cnt (bs.take i) v + (if blk bs i v then 1 else 0) := by
  rw [List.take_add_one, cnt_append]
  have : bs[i]? = some bs[i] := List.getElem?_eq_getElem hi
  simp only [blk, this, Option.toList_some, Option.getD_some]
  by_cases hb : bs[i] v <;> simp [cnt, List.filter, hb]

theorem cnt_take_length (bs : List (Nat → Bool)) (v : Nat) : cnt (bs.take bs.length) v = cnt bs v := by
  rw [List.take_length]

theorem cnt_take_mono (bs : List (Nat → Bool)) (v : Nat) :
    ∀ k i, i + k ≤ bs.length → cnt (bs.take i) v ≤ cnt (bs.take (i + k)) v
  | 0, i, _ => Nat.le_refl _
  | k + 1, i, hk => by
    have h1 := cnt_take_mono bs v k i (by omega)
    have h2 := cnt_take_succ bs (i + k) v (by omega)
    rw [show i + (k + 1) = i + k + 1 by omega, h2]
    omega

theorem cnt_take_le (bs : List (Nat → Bool)) (v i : Nat) (hi : i ≤ bs.length) :
    cnt (bs.take i) v ≤ cnt bs v := by
  have := cnt_take_mono bs v (bs.length - i) i (by omega)
  rw [show i + (bs.length - i) = bs.length by omega, cnt_take_length] at this
  exact this

/-- A list containing two distinct elements has length at least two. -/
theorem two_le_length {l : List Nat} {a b : Nat} (hab : a ≠ b) (ha : a ∈ l) (hb : b ∈ l) :
    2 ≤ l.length := by
  match l with
  | [] => simp at ha
  | [c] =>
    simp at ha hb
    omega
  | _ :: _ :: _ => simp

/-- Filtering with a smaller predicate gives a list that is no longer. -/
theorem filter_length_le {l : List Nat} {P Q : Nat → Bool}
    (hPQ : ∀ x ∈ l, Q x = true → P x = true) : (l.filter Q).length ≤ (l.filter P).length := by
  induction l with
  | nil => simp
  | cons z zs ih =>
    have hz := hPQ z (List.mem_cons_self)
    have ih' := ih (fun x hx => hPQ x (List.mem_cons_of_mem _ hx))
    by_cases hq : Q z = true
    · rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos (hz hq)]
      simp only [List.length_cons]; omega
    · by_cases hp : P z = true
      · rw [List.filter_cons_of_neg hq, List.filter_cons_of_pos hp]
        simp only [List.length_cons]; omega
      · rw [List.filter_cons_of_neg hq, List.filter_cons_of_neg hp]; exact ih'

/-- Filtering with a smaller predicate that misses a witness gives a shorter list. -/
theorem filter_length_lt {l : List Nat} {P Q : Nat → Bool} (hPQ : ∀ x ∈ l, Q x = true → P x = true)
    {w : Nat} (hw : w ∈ l) (hPw : P w = true) (hQw : Q w = false) :
    (l.filter Q).length + 1 ≤ (l.filter P).length := by
  induction l with
  | nil => simp at hw
  | cons y ys ih =>
    have hPQ' : ∀ x ∈ ys, Q x = true → P x = true := fun x hx => hPQ x (List.mem_cons_of_mem _ hx)
    have hy := hPQ y (List.mem_cons_self)
    by_cases hwy : w = y
    · subst hwy
      have hmono := filter_length_le hPQ'
      rw [List.filter_cons_of_neg (by simp [hQw]), List.filter_cons_of_pos hPw]
      simp only [List.length_cons]; omega
    · have hw' : w ∈ ys := by
        rcases List.mem_cons.mp hw with h | h
        · exact absurd h hwy
        · exact h
      have ih' := ih hPQ' hw'
      by_cases hq : Q y = true
      · rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos (hy hq)]
        simp only [List.length_cons]; omega
      · by_cases hp : P y = true
        · rw [List.filter_cons_of_neg hq, List.filter_cons_of_pos hp]
          simp only [List.length_cons]; omega
        · rw [List.filter_cons_of_neg hq, List.filter_cons_of_neg hp]; exact ih'

/-- The pair `a, b` lies together in one of the first `k` blocks. -/
def metIn (bs : List (Nat → Bool)) (k a b : Nat) : Bool :=
  (List.range k).any (fun j => blk bs j a && blk bs j b)

theorem metIn_iff (bs : List (Nat → Bool)) (k a b : Nat) :
    metIn bs k a b = true ↔ ∃ j < k, blk bs j a = true ∧ blk bs j b = true := by
  simp [metIn, List.any_eq_true, List.mem_range]

/-- The partners of `v` among `0, …, u-1` that it has not met in the first `k` blocks. -/
def unmetIn (bs : List (Nat → Bool)) (u k v : Nat) : Nat :=
  ((List.range u).filter (fun w => w != v && !metIn bs k v w)).length

/-- Each block through `v` uses up a partner that `v` had not met before. -/
theorem cnt_unmet_step (u : Nat) (bs : List (Nat → Bool)) (ha : Linear u bs) (v k : Nat)
    (hk : k < bs.length) :
    cnt (bs.take (k + 1)) v + unmetIn bs u (k + 1) v ≤ cnt (bs.take k) v + unmetIn bs u k v := by
  rw [cnt_take_succ bs k v hk]
  have hmono : ∀ x ∈ List.range u,
      (x != v && !metIn bs (k + 1) v x) = true → (x != v && !metIn bs k v x) = true := by
    intro x _ hx
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hx ⊢
    refine ⟨hx.1, ?_⟩
    cases hm : metIn bs k v x
    · rfl
    · exfalso
      rw [metIn_iff] at hm
      obtain ⟨j, hj, h1, h2⟩ := hm
      have : metIn bs (k + 1) v x = true := (metIn_iff _ _ _ _).mpr ⟨j, by omega, h1, h2⟩
      rw [this] at hx
      exact absurd hx.2 (by simp)
  by_cases hv : blk bs k v = true
  · simp only [hv, if_true]
    obtain ⟨a, b, hab, ha1, hb1⟩ := ha.two k hk
    -- a partner `w ≠ v` of `v` in the block
    have hw : ∃ w, w ≠ v ∧ blk bs k w = true := by
      by_cases hav : a = v
      · exact ⟨b, fun hbv => hab (hav.trans hbv.symm), hb1⟩
      · exact ⟨a, hav, ha1⟩
    obtain ⟨w, hwv, hwk⟩ := hw
    have hwu : w < u := ha.sub k hk w hwk
    have hnotmet : metIn bs k v w = false := by
      cases hm : metIn bs k v w
      · rfl
      · exfalso
        rw [metIn_iff] at hm
        obtain ⟨j, hj, h1, h2⟩ := hm
        exact ha.lin j k (by omega) hk (by omega) v w (fun h => hwv h.symm) h1 h2 hv hwk
    have hmet : metIn bs (k + 1) v w = true := (metIn_iff _ _ _ _).mpr ⟨k, by omega, hv, hwk⟩
    have := filter_length_lt (l := List.range u)
      (P := fun x => x != v && !metIn bs k v x) (Q := fun x => x != v && !metIn bs (k + 1) v x)
      hmono (w := w) (List.mem_range.mpr hwu) (by simp [hwv, hnotmet]) (by simp [hmet])
    unfold unmetIn
    omega
  · simp only [Bool.not_eq_true] at hv
    simp only [hv]
    have := filter_length_le (l := List.range u)
      (P := fun x => x != v && !metIn bs k v x) (Q := fun x => x != v && !metIn bs (k + 1) v x)
      hmono
    unfold unmetIn
    simp
    omega

/-- The number of blocks through `v` is at most its count so far plus its unmet partners. -/
theorem cnt_le_unmet (u : Nat) (bs : List (Nat → Bool)) (ha : Linear u bs) (v : Nat) :
    ∀ m i, i + m = bs.length → cnt bs v ≤ cnt (bs.take i) v + unmetIn bs u i v
  | 0, i, him => by
    rw [show i = bs.length by omega, cnt_take_length]
    omega
  | m + 1, i, him => by
    have h1 := cnt_le_unmet u bs ha v m (i + 1) (by omega)
    have h2 := cnt_unmet_step u bs ha v i (by omega)
    omega

end SweepCheck
