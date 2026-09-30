/-
Soundness of the checker: if `checkLog u h d = true`, then no admissible sequence of blocks has a
solution of its linear system that satisfies the parity rule.

The proof follows the actual sequence of blocks and the actual solution down the log.  At every
node visited, the state of the checker agrees with the actual sequence (`Inv`): the counts, the
meeting relation and the parity records are those of the blocks decided so far, and every row
collected so far is satisfied by the actual solution.  At a node where the actual sequence would
leave the log, one of the rules is violated, and at a certificate the rows cannot all be
satisfied.  Either way there is a contradiction.
-/
import SweepCheck.Checker
import SweepCheck.Lemmas

namespace SweepCheck

/-- The assignment of the variables `p v ↦ v`, `t v ↦ u + v`, `W ↦ 2u`, `x i ↦ 2u + 1 + i`. -/
def asg (u : Nat) (p t x : Nat → Int) (W : Int) : Nat → Int := fun k =>
  if k < u then p k
  else if k < 2 * u then t (k - u)
  else if k = 2 * u then W
  else x (k - (2 * u + 1))

section asg
variable {u : Nat} {p t x : Nat → Int} {W : Int}

theorem asg_p {v : Nat} (hv : v < u) : asg u p t x W v = p v := by
  simp [asg, hv]

theorem asg_t {v : Nat} (hv : v < u) : asg u p t x W (u + v) = t v := by
  unfold asg
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem asg_w : asg u p t x W (2 * u) = W := by
  unfold asg
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem asg_x (i : Nat) : asg u p t x W (2 * u + 1 + i) = x i := by
  unfold asg
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

end asg

/-- The parity of an integer, as `0` or `1`. -/
def par (a : Int) : Nat := if a % 2 = 0 then 0 else 1

theorem par_lt (a : Int) : par a < 2 := by
  unfold par; split <;> omega

theorem par_rel (a b : Int) (ca cb : Nat) (h : (a + (ca : Int)) % 2 = (b + (cb : Int)) % 2) :
    (par a + par b) % 2 = (ca + cb) % 2 := by
  unfold par
  split <;> split <;> omega

theorem sat_lo {a : List Int} {l : Int} {z : Nat → Int} (h : l ≤ dot a z) :
    Row.Sat ⟨a, some l, none⟩ z := by
  refine ⟨fun l' hl => ?_, fun m hm => ?_⟩
  · simp only [Option.some.injEq] at hl; subst hl; exact h
  · simp at hm

theorem sat_eq {a : List Int} {z : Nat → Int} (h : dot a z = 0) :
    Row.Sat ⟨a, some 0, some 0⟩ z := by
  refine ⟨fun l' hl => ?_, fun m hm => ?_⟩
  · simp only [Option.some.injEq] at hl; subst hl; show (0 : Int) ≤ dot a z; omega
  · simp only [Option.some.injEq] at hm; subst hm; show dot a z ≤ 0; omega

section sound
variable (u h : Nat) (bs : List (Nat → Bool)) (p t x : Nat → Int) (W : Int)

/-- The checker's state agrees with the actual sequence of blocks and the actual solution. -/
structure Inv (st : St) : Prop where
  hu : st.u = u
  hh : st.h = h
  hi : st.i ≤ bs.length
  hc : ∀ v, st.c v = cnt (bs.take st.i) v
  hmet : ∀ a b, st.met a b = metIn bs st.i a b
  hpar : ∀ v, par (t v) = (par (t (st.rep v)) + st.off v) % 2
  hrows : ∀ r ∈ st.rows, r.Sat (asg u p t x W)

/-- The invariant for each position in the log. -/
def MInv : Mode → St → Prop
  | .bnd, st => Inv u h bs p t x W st
  | .term, st => ∀ r ∈ st.rows, r.Sat (asg u p t x W)
  | .elem v S, st => Inv u h bs p t x W st ∧ st.i < bs.length ∧ v ≤ u ∧
      ∀ w, w ∈ S ↔ w < v ∧ blk bs st.i w = true

variable {u h bs p t x W}

theorem chkCert_sound {st : St} {d : ByteArray} {pos q : Nat} (hc : chkCert st d pos = some q)
    (hrows : ∀ r ∈ st.rows, r.Sat (asg u p t x W)) : False := by
  unfold chkCert at hc
  split at hc
  · simp at hc
  · split at hc
    · simp at hc
    · split at hc
      · rename_i cert _ _ hok
        exact certOK_sound st.rows cert _ hrows hok
      · simp at hc

theorem dot_piForm {st : St} (hinv : Inv u h bs p t x W st) {v : Nat} (hv : v < u) :
    dot (st.piForm v) (asg u p t x W) = t v - x st.i + (st.c v : Int) * p v := by
  simp only [St.piForm, St.tI, St.xI, St.pI, dot_form, hinv.hu, List.map, List.sum_cons,
    List.sum_nil]
  rw [asg_t hv, asg_x, asg_p hv]
  omega

theorem init_inv (hu2 : 2 ≤ u) (hs : System u h bs p t x W) :
    Inv u h bs p t x W (St.init u h) := by
  refine ⟨rfl, rfl, Nat.zero_le _, fun v => by simp [St.init, cnt], fun a b => by
    simp [St.init, metIn], fun v => by simp [St.init]; have := par_lt (t v); omega, ?_⟩
  intro r hr
  simp only [St.init, List.mem_reverse, baseRows, List.mem_append, List.mem_cons,
    List.mem_map, List.mem_range, List.mem_flatten, List.not_mem_nil, or_false] at hr
  rcases hr with (((hr | ⟨j, hj, hr⟩) | hr) | ⟨l, ⟨v, hv, hl⟩, hr⟩) | hr
  · subst hr
    apply sat_lo
    simp only [dot_form, List.map, List.sum_cons, List.sum_nil]
    rw [asg_p (by omega)]
    have := hs.p0
    omega
  · subst hr
    apply sat_lo
    simp only [dot_form, List.map, List.sum_cons, List.sum_nil]
    rw [asg_p (by omega), asg_p (by omega)]
    have := hs.pstep j (by omega)
    omega
  · subst hr
    apply sat_lo
    simp only [dot_form, List.map, List.sum_cons, List.sum_nil]
    rw [asg_p (by omega)]
    have := hs.p1
    omega
  · subst hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr | hr <;> subst hr <;> apply sat_lo <;>
      simp only [dot_form, List.map, List.sum_cons, List.sum_nil]
    · rw [asg_t hv]; have := hs.t0 v hv; omega
    · rw [asg_p hv, asg_t hv]; have := hs.t1 v hv; omega
    · rw [asg_t hv, asg_p hv, asg_w]; have := hs.tmax v hv; omega
  · subst hr
    apply sat_lo
    simp only [dot_form, List.map, List.sum_cons, List.sum_nil]
    rw [asg_w, asg_p (by omega), Int.neg_mul]
    have := hs.wlow
    omega

theorem cap_false (ha : Admissible u h bs) {st : St} (hinv : Inv u h bs p t x W st) {v : Nat}
    (hcap : st.capOK v = true) : False := by
  simp only [St.capOK, Bool.and_eq_true, decide_eq_true_eq] at hcap
  obtain ⟨hv, hlt⟩ := hcap
  rw [hinv.hu] at hv
  have hunmet : st.unmet v = unmetIn bs u st.i v := by
    simp only [St.unmet, unmetIn, hinv.hu, hinv.hmet]
  rw [hunmet, hinv.hc, hinv.hh] at hlt
  have h1 := cnt_le_unmet u bs ha.toLinear v (bs.length - st.i) st.i (by have := hinv.hi; omega)
  have h2 := (ha.deg v hv).1
  omega

theorem full_of_end (ha : Admissible u h bs) {st : St} (hinv : Inv u h bs p t x W st)
    (hend : st.i = bs.length) : st.full = true := by
  simp only [St.full, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro v hv
  rw [hinv.hu] at hv
  rw [hinv.hc, hinv.hh, hend, cnt_take_length]
  exact (ha.deg v hv).1

theorem addEnd_rows (hs : System u h bs p t x W) {st : St} (hinv : Inv u h bs p t x W st)
    (hend : st.i = bs.length) : ∀ r ∈ st.addEnd.rows, r.Sat (asg u p t x W) := by
  intro r hr
  simp only [St.addEnd, List.mem_append, List.mem_reverse, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨v, hv, rfl⟩ | hr
  · rw [hinv.hu] at hv
    apply sat_lo
    simp only [St.tI, St.pI, St.wI, dot_form, List.map, List.sum_cons, List.sum_nil, hinv.hu]
    rw [asg_t hv, asg_p hv, asg_w, hinv.hc, hend, cnt_take_length]
    have := hs.last v hv
    omega
  · exact hinv.hrows r hr

theorem allMet_false (ha : Admissible u h bs) {st : St} (hinv : Inv u h bs p t x W st)
    (hlt : st.i < bs.length) (hall : st.allMet = true) : False := by
  obtain ⟨a, b, hab, ha1, hb1⟩ := ha.two st.i hlt
  have hau := ha.sub st.i hlt a ha1
  have hbu := ha.sub st.i hlt b hb1
  simp only [St.allMet, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hall
  rw [hinv.hu] at hall
  rcases hall a hau b hbu with h | h
  · exact hab h
  · rw [hinv.hmet, metIn_iff] at h
    obtain ⟨j, hj, h1, h2⟩ := h
    exact ha.lin j st.i (by omega) hlt (by omega) a b hab h1 h2 ha1 hb1

theorem addX_inv (hs : System u h bs p t x W) {st : St} (hinv : Inv u h bs p t x W st)
    (hlt : st.i < bs.length) :
    MInv u h bs p t x W (.elem 0 []) st.addX := by
  refine ⟨⟨hinv.hu, hinv.hh, hinv.hi, hinv.hc, hinv.hmet, hinv.hpar, ?_⟩, hlt, Nat.zero_le _,
    fun w => by simp⟩
  intro r hr
  simp only [St.addX, List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · apply sat_lo
    simp only [St.wI, St.xI, dot_form, List.map, List.sum_cons, List.sum_nil, hinv.hu]
    rw [asg_w, asg_x]
    have := hs.xmax st.i hlt
    omega
  · split
    · rename_i h0
      apply sat_lo
      simp only [St.xI, dot_form, List.map, List.sum_cons, List.sum_nil, hinv.hu]
      rw [asg_x]
      have := hs.x0 (by omega)
      rw [h0] at *
      omega
    · rename_i h0
      apply sat_lo
      simp only [St.xI, dot_form, List.map, List.sum_cons, List.sum_nil, hinv.hu]
      rw [asg_x, asg_x]
      have := hs.xstep (st.i - 1) (by omega)
      rw [show st.i - 1 + 1 = st.i by omega] at this
      omega
  · exact hinv.hrows r hr

theorem leave_inv (hs : System u h bs p t x W) {st : St} {v : Nat} {S : List Nat}
    (hm : MInv u h bs p t x W (.elem v S) st) (hvu : v < u) (hout : blk bs st.i v = false) :
    MInv u h bs p t x W (.elem (v + 1) S) (st.leave v) := by
  obtain ⟨hinv, hlt, _, hS⟩ := hm
  refine ⟨⟨hinv.hu, hinv.hh, hinv.hi, hinv.hc, hinv.hmet, hinv.hpar, ?_⟩, hlt, by omega, ?_⟩
  · intro r hr
    simp only [St.leave, St.addRow, List.mem_cons] at hr
    rcases hr with rfl | hr
    · apply sat_lo
      rw [dot_piForm hinv hvu, hinv.hc]
      have := hs.miss st.i hlt v hvu hout
      omega
    · exact hinv.hrows r hr
  · show ∀ w, w ∈ S ↔ w < v + 1 ∧ blk bs st.i w = true
    intro w
    rw [hS w]
    constructor
    · intro hw; exact ⟨by omega, hw.2⟩
    · intro hw
      refine ⟨?_, hw.2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hw.1 with h1 | h1
      · exact h1
      · exfalso
        have h2 := hw.2
        rw [h1, hout] at h2
        exact absurd h2 (by simp)

theorem join_ok (ha : Admissible u h bs) (hs : System u h bs p t x W) (hp : ParityOK bs t)
    {st : St} {v : Nat} {S : List Nat}
    (hm : MInv u h bs p t x W (.elem v S) st) (hvu : v < u) (hin : blk bs st.i v = true) :
    st.canJoin v S = true ∧ MInv u h bs p t x W (.elem (v + 1) (S ++ [v])) (st.join v S) := by
  obtain ⟨hinv, hlt, _, hS⟩ := hm
  -- the members of S are in the block, below v
  have hSmem : ∀ s ∈ S, s < v ∧ blk bs st.i s = true := fun s hs' => (hS s).mp hs'
  -- no member of S has met v
  have hnm : ∀ s ∈ S, st.met v s = false := by
    intro s hs'
    obtain ⟨hsv, hsb⟩ := hSmem s hs'
    rw [hinv.hmet]
    cases hmt : metIn bs st.i v s
    · rfl
    · exfalso
      rw [metIn_iff] at hmt
      obtain ⟨j, hj, h1, h2⟩ := hmt
      exact ha.lin j st.i (by omega) hlt (by omega) v s (by omega) h1 h2 hin hsb
  -- the true parity relation between v and a member of S
  have hrel : ∀ s ∈ S, (par (t v) + par (t s)) % 2 = (st.c v + st.c s) % 2 := by
    intro s hs'
    rw [hinv.hc, hinv.hc]
    exact par_rel _ _ _ _ (hp st.i hlt v s hin (hSmem s hs').2)
  constructor
  · -- the rules allow v to join
    simp only [St.canJoin, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨?_, fun s hs' => by simp [hnm s hs']⟩, ?_⟩
    · rw [hinv.hu, hinv.hc]
      have h1 := cnt_take_succ bs st.i v hlt
      rw [hin] at h1
      have h2 := cnt_take_le bs v (st.i + 1) (by omega)
      have h3 := (ha.deg v hvu).2
      simp at h1
      omega
    · split
      · rfl
      · rename_i s rest
        have hsS : s ∈ s :: rest := List.mem_cons_self
        have hr := hrel s hsS
        simp only [St.parityOK, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
        by_cases hrep : st.rep v = st.rep s
        · right
          have h1 := hinv.hpar v
          have h2 := hinv.hpar s
          rw [hrep] at h1
          have := par_lt (t (st.rep s))
          omega
        · left; exact hrep
  · -- the state after joining
    have hjoin : ∀ st' : St, st'.u = st.u → st'.h = st.h → st'.i = st.i → st'.c = st.c →
        st'.met = st.met → st'.rows = st.rows →
        (∀ w, par (t w) = (par (t (st'.rep w)) + st'.off w) % 2) →
        MInv u h bs p t x W (.elem (v + 1) (S ++ [v])) (st'.addRow ⟨st.piForm v, some 0, some 0⟩) := by
      intro st' e1 e2 e3 e4 e5 e6 hpar'
      refine ⟨⟨by simp [St.addRow, e1, hinv.hu], by simp [St.addRow, e2, hinv.hh],
        by simp [St.addRow, e3]; exact hinv.hi,
        by intro w; simp [St.addRow, e3, e4, hinv.hc],
        by intro a b; simp [St.addRow, e3, e5, hinv.hmet], by simpa [St.addRow] using hpar', ?_⟩,
        by simp [St.addRow, e3]; exact hlt, by omega, ?_⟩
      · intro r hr
        simp only [St.addRow, List.mem_cons, e6] at hr
        rcases hr with rfl | hr
        · apply sat_eq
          rw [dot_piForm hinv hvu, hinv.hc]
          have := hs.hit st.i hlt v hvu hin
          omega
        · exact hinv.hrows r hr
      · intro w
        simp only [St.addRow, e3, List.mem_append, List.mem_singleton]
        rw [hS w]
        constructor
        · rintro (hw | rfl)
          · exact ⟨by omega, hw.2⟩
          · exact ⟨by omega, hin⟩
        · intro hw
          rcases Nat.lt_succ_iff_lt_or_eq.mp hw.1 with h1 | h1
          · exact Or.inl ⟨h1, hw.2⟩
          · exact Or.inr h1
    unfold St.join
    split
    · exact hjoin st rfl rfl rfl rfl rfl rfl hinv.hpar
    · rename_i s rest
      have hsS : s ∈ s :: rest := List.mem_cons_self
      have hr := hrel s hsS
      unfold St.joinPar
      split
      · exact hjoin st rfl rfl rfl rfl rfl rfl hinv.hpar
      · rename_i hne
        dsimp only
        refine hjoin _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        all_goals try rfl
        intro w
        have hw := hinv.hpar w
        have hv' := hinv.hpar v
        have hs' := hinv.hpar s
        have := par_lt (t (st.rep s))
        have := par_lt (t (st.rep v))
        have := par_lt (t w)
        dsimp only
        by_cases hwv : st.rep w = st.rep v
        · rw [if_pos hwv, if_pos hwv]
          rw [hwv] at hw
          omega
        · rw [if_neg hwv, if_neg hwv]
          exact hw

theorem next_inv (ha : Admissible u h bs) {st : St} {S : List Nat}
    (hm : MInv u h bs p t x W (.elem st.u S) st) :
    2 ≤ S.length ∧ Inv u h bs p t x W (st.next S) := by
  obtain ⟨hinv, hlt, _, hS⟩ := hm
  have hSb : ∀ w, S.contains w = blk bs st.i w := by
    intro w
    apply Bool.eq_iff_iff.mpr
    rw [List.contains_iff_mem, hS w, hinv.hu]
    constructor
    · exact fun hw => hw.2
    · intro hb; exact ⟨ha.sub st.i hlt w hb, hb⟩
  constructor
  · obtain ⟨a, b, hab, ha1, hb1⟩ := ha.two st.i hlt
    have haS : a ∈ S := by rw [← List.contains_iff_mem, hSb]; exact ha1
    have hbS : b ∈ S := by rw [← List.contains_iff_mem, hSb]; exact hb1
    exact two_le_length hab haS hbS
  · refine ⟨hinv.hu, hinv.hh, by simp [St.next]; omega, ?_, ?_, hinv.hpar, hinv.hrows⟩
    · intro w
      simp only [St.next, hSb w]
      rw [cnt_take_succ bs st.i w hlt, hinv.hc]
      split <;> simp
    · intro a b
      show (st.met a b || (S.contains a && S.contains b)) = metIn bs (st.i + 1) a b
      rw [hSb a, hSb b, hinv.hmet]
      apply Bool.eq_iff_iff.mpr
      rw [Bool.or_eq_true, Bool.and_eq_true, metIn_iff, metIn_iff]
      constructor
      · rintro (⟨j, hj, h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨j, by omega, h1, h2⟩
        · exact ⟨st.i, by omega, h1, h2⟩
      · rintro ⟨j, hj, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
        · exact Or.inl ⟨j, hj', h1, h2⟩
        · subst hj'; exact Or.inr ⟨h1, h2⟩

theorem chk_sound (ha : Admissible u h bs) (hs : System u h bs p t x W) (hp : ParityOK bs t)
    (d : ByteArray) :
    ∀ (fuel : Nat) (mode : Mode) (st : St) (pos q : Nat),
      chk fuel mode st d pos = some q → MInv u h bs p t x W mode st → False := by
  intro fuel
  induction fuel with
  | zero => intro mode st pos q hc; simp [chk] at hc
  | succ fuel ih =>
    intro mode st pos q hc hm
    cases mode with
    | bnd =>
      simp only [chk] at hc
      split at hc
      · simp at hc
      · rename_i tag p1 _
        split at hc
        · exact chkCert_sound hc hm.hrows
        · split at hc
          · split at hc
            · simp at hc
            · rename_i v p2 _
              split at hc
              · rename_i hcap
                exact cap_false ha hm hcap
              · simp at hc
          · split at hc
            · -- the node is expanded
              split at hc
              · simp at hc
              · rename_i p2 hr1
                by_cases hend : st.i = bs.length
                · have hfull := full_of_end ha hm hend
                  rw [if_pos hfull] at hr1
                  exact ih .term st.addEnd p1 p2 hr1 (addEnd_rows hs hm hend)
                · have hlt : st.i < bs.length := by have := hm.hi; omega
                  split at hc
                  · rename_i hall
                    exact allMet_false ha hm hlt hall
                  · exact ih (.elem 0 []) st.addX p2 q hc (addX_inv hs hm hlt)
            · simp at hc
    | term =>
      simp only [chk] at hc
      split at hc
      · simp at hc
      · split at hc
        · exact chkCert_sound hc hm
        · simp at hc
    | elem v S =>
      simp only [chk] at hc
      obtain ⟨hinv, hlt, hvu, hS⟩ := hm
      split at hc
      · rename_i hveq
        have hm' : MInv u h bs p t x W (.elem st.u S) st := by
          rw [← hveq]; exact ⟨hinv, hlt, hvu, hS⟩
        obtain ⟨h2, hnext⟩ := next_inv ha hm'
        split at hc
        · omega
        · exact ih .bnd (st.next S) pos q hc hnext
      · rename_i hvne
        have hvu' : v < u := by rw [hinv.hu] at hvne; omega
        split at hc
        · simp at hc
        · rename_i tag p1 _
          split at hc
          · exact chkCert_sound hc hinv.hrows
          · split at hc
            · split at hc
              · simp at hc
              · rename_i p2 hr1
                cases hb : blk bs st.i v
                · exact ih (.elem (v + 1) S) (st.leave v) p2 q hc
                    (leave_inv hs ⟨hinv, hlt, hvu, hS⟩ hvu' hb)
                · obtain ⟨hcj, hm2⟩ := join_ok ha hs hp ⟨hinv, hlt, hvu, hS⟩ hvu' hb
                  rw [if_pos hcj] at hr1
                  exact ih (.elem (v + 1) (S ++ [v])) (st.join v S) p1 p2 hr1 hm2
            · simp at hc

end sound

/-- **Soundness of the checker.**  If the log `d` is accepted for `(u, h)`, then no sequence of
blocks satisfying rules (R1)–(R4) has an integer solution of the linear system. -/
theorem checkLog_sound (u h : Nat) (hu2 : 2 ≤ u) (d : ByteArray) (hd : checkLog u h d = true)
    (bs : List (Nat → Bool)) (p t x : Nat → Int) (W : Int)
    (ha : Admissible u h bs) (hs : System u h bs p t x W) (hp : ParityOK bs t) : False := by
  unfold checkLog at hd
  simp only [beq_iff_eq] at hd
  exact chk_sound ha hs hp d 100000 .bnd (St.init u h) 0 d.size hd (init_inv hu2 hs)

end SweepCheck
