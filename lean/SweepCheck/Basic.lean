/-
Linear forms, rows and Farkas certificates.

A linear form is a list of integer coefficients `[a₀, a₁, …]`; its value at an assignment
`z : Nat → Int` is `a₀ z₀ + a₁ z₁ + ⋯`.  A row is a form with an optional lower and an optional
upper bound.  A certificate is a list of pairs `(k, y)`, meaning `y` times the `k`-th row (rows
are counted from the head of the list).  It is valid when the weighted sum of the forms is the
zero form and the weighted sum of the bounds (the lower bound where `y > 0`, the upper bound where
`y < 0`) is positive.  `certOK_sound` shows that a valid certificate rules out every assignment
satisfying all the rows.
-/

namespace SweepCheck

/-- The value of a linear form at an assignment. -/
def dot : List Int → (Nat → Int) → Int
  | [], _ => 0
  | c :: cs, z => c * z 0 + dot cs (fun k => z (k + 1))

/-- Sum of two forms (the shorter one padded with zeros). -/
def addPad : List Int → List Int → List Int
  | [], b => b
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addPad as bs

/-- A multiple of a form. -/
def scale (c : Int) (a : List Int) : List Int := a.map (fun x => c * x)

/-- The form `a · z_k`. -/
def single : Nat → Int → List Int
  | 0, a => [a]
  | k + 1, a => 0 :: single k a

/-- The form `∑ a · z_k` over a list of pairs `(k, a)`. -/
def form : List (Nat × Int) → List Int
  | [] => []
  | (k, a) :: rest => addPad (single k a) (form rest)

theorem dot_addPad (a b : List Int) (z : Nat → Int) :
    dot (addPad a b) z = dot a z + dot b z := by
  induction a generalizing b z with
  | nil => simp [addPad, dot]
  | cons x xs ih =>
    cases b with
    | nil => simp [addPad, dot]
    | cons y ys =>
      simp only [addPad, dot, ih]
      rw [Int.add_mul]
      omega

theorem dot_scale (c : Int) (a : List Int) (z : Nat → Int) :
    dot (scale c a) z = c * dot a z := by
  induction a generalizing z with
  | nil => simp [scale, dot]
  | cons x xs ih =>
    simp only [scale, List.map, dot] at *
    rw [ih, Int.mul_add, Int.mul_assoc]

theorem dot_single (k : Nat) (a : Int) (z : Nat → Int) : dot (single k a) z = a * z k := by
  induction k generalizing z with
  | zero => simp [single, dot]
  | succ k ih => simp [single, dot, ih]

theorem dot_form (l : List (Nat × Int)) (z : Nat → Int) :
    dot (form l) z = (l.map (fun e => e.2 * z e.1)).sum := by
  induction l with
  | nil => simp [form, dot]
  | cons e rest ih =>
    obtain ⟨k, a⟩ := e
    simp [form, dot_addPad, dot_single, ih]

theorem dot_zero (a : List Int) (z : Nat → Int) (h : a.all (fun x => x == 0) = true) :
    dot a z = 0 := by
  induction a generalizing z with
  | nil => simp [dot]
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [dot, h.1, ih _ h.2]

/-- A row: `lo ≤ form ≤ hi`, each bound optional. -/
structure Row where
  a : List Int
  lo : Option Int
  hi : Option Int

/-- The assignment `z` satisfies the row. -/
def Row.Sat (r : Row) (z : Nat → Int) : Prop :=
  (∀ l, r.lo = some l → l ≤ dot r.a z) ∧ (∀ m, r.hi = some m → dot r.a z ≤ m)

/-- The `k`-th row, counted from the head. -/
def nth : List Row → Nat → Option Row
  | [], _ => none
  | r :: _, 0 => some r
  | _ :: rs, k + 1 => nth rs k

theorem nth_mem : ∀ (rows : List Row) (k : Nat) (r : Row), nth rows k = some r → r ∈ rows
  | [], _, _, h => by simp [nth] at h
  | r :: rs, 0, r', h => by simp [nth] at h; simp [h]
  | _ :: rs, k + 1, r', h => by
    simp only [nth] at h
    exact List.mem_cons_of_mem _ (nth_mem rs k r' h)

/-- Weighted sum of the rows named in a certificate: the form and the bound. -/
def certAcc (rows : List Row) : List (Nat × Int) → Option (List Int × Int)
  | [] => some ([], 0)
  | (k, y) :: rest =>
    match certAcc rows rest with
    | none => none
    | some (vec, b) =>
      match nth rows k with
      | none => none
      | some r =>
        if 0 < y then
          match r.lo with
          | some l => some (addPad (scale y r.a) vec, b + y * l)
          | none => none
        else if y < 0 then
          match r.hi with
          | some m => some (addPad (scale y r.a) vec, b + y * m)
          | none => none
        else some (vec, b)

/-- A certificate is valid: the weighted form vanishes and the weighted bound is positive. -/
def certOK (rows : List Row) (cert : List (Nat × Int)) : Bool :=
  match certAcc rows cert with
  | some (vec, b) => vec.all (fun x => x == 0) && decide (0 < b)
  | none => false

theorem certAcc_le (rows : List Row) (z : Nat → Int) (hsat : ∀ r ∈ rows, r.Sat z) :
    ∀ (cert : List (Nat × Int)) (vec : List Int) (b : Int),
      certAcc rows cert = some (vec, b) → b ≤ dot vec z
  | [], vec, b, h => by
    simp only [certAcc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [dot]
  | (k, y) :: rest, vec, b, h => by
    simp only [certAcc] at h
    split at h
    · simp at h
    · rename_i vec0 b0 hrest
      have ih := certAcc_le rows z hsat rest vec0 b0 hrest
      split at h
      · simp at h
      · rename_i r hr
        have hs := hsat r (nth_mem rows k r hr)
        split at h
        · rename_i hy
          split at h
          · rename_i l hl
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [dot_addPad, dot_scale]
            have h1 := hs.1 l hl
            have h2 : y * l ≤ y * dot r.a z := Int.mul_le_mul_of_nonneg_left h1 (by omega)
            omega
          · simp at h
        · rename_i hy
          split at h
          · rename_i hy'
            split at h
            · rename_i m hm
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [dot_addPad, dot_scale]
              have h1 := hs.2 m hm
              have h2 : y * m ≤ y * dot r.a z :=
                Int.mul_le_mul_of_nonpos_left (by omega) h1
              omega
            · simp at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ih

/-- A valid certificate rules out every assignment that satisfies all the rows. -/
theorem certOK_sound (rows : List Row) (cert : List (Nat × Int)) (z : Nat → Int)
    (hsat : ∀ r ∈ rows, r.Sat z) (h : certOK rows cert = true) : False := by
  unfold certOK at h
  split at h
  · rename_i vec b hacc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have h1 := certAcc_le rows z hsat cert vec b hacc
    have h2 := dot_zero vec z h.1
    omega
  · simp at h

end SweepCheck
