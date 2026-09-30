/-
The checker for the proof logs written by `sweep_search.py --emit`.

The search builds a sequence of blocks (subsets of the ranks `0, …, u-1` of the primes) from left
to right.  It keeps the number `c v` of blocks so far that contain `v`, the relation `met a b`
(some block so far contains `a` and `b`), a record of the parity relations imposed so far
(`rep`, `off`: the parity of `t v` equals the parity of `t (rep v)` plus `off v`), and the list
of rows of the linear system collected so far, the newest first.

The variables of the linear system are numbered `p v ↦ v`, `t v ↦ u + v`, `W ↦ 2u` and
`x i ↦ 2u + 1 + i`.

The log is a sequence of unsigned LEB128 numbers.  At a block boundary it holds one of
`0` (a certificate for the current rows), `1 v` (the prime `v` can no longer reach `h` blocks),
`2` (the node is expanded: first, if every prime has `h` blocks, the interval may end here, and
the rows saying so are refuted by a certificate; then, unless every pair of primes has met, a new
block is started).  Inside a block it holds `0` (a certificate) or `3` (the node is expanded: the
next prime joins the block if the rules allow it, and then it stays out).  A certificate is
`0 m k₁ y₁ … k_m y_m` with the multipliers `y` zigzag-encoded.  When a block has received its
last decision it is closed without reading anything: if it has fewer than two primes the branch
is dead, and otherwise the next block boundary follows.
-/
import SweepCheck.Basic

namespace SweepCheck

/-- The state of the search between two decisions. -/
structure St where
  u : Nat
  h : Nat
  i : Nat
  c : Nat → Nat
  met : Nat → Nat → Bool
  rep : Nat → Nat
  off : Nat → Nat
  rows : List Row

def St.pI (_ : St) (v : Nat) : Nat := v
def St.tI (st : St) (v : Nat) : Nat := st.u + v
def St.wI (st : St) : Nat := 2 * st.u
def St.xI (st : St) (i : Nat) : Nat := 2 * st.u + 1 + i

/-- The rows valid for every interval, in the order the search adds them (oldest first). -/
def baseRows (u h : Nat) : List Row :=
  let W := 2 * u
  [⟨form [(0, 1)], some 3, none⟩] ++
  (List.range (u - 1)).map (fun j => ⟨form [(j + 1, 1), (j, -1)], some 2, none⟩) ++
  [⟨form [(1, 1)], some (2 * (u : Int) - 1), none⟩] ++
  ((List.range u).map (fun v =>
      [⟨form [(u + v, 1)], some 0, none⟩,
       ⟨form [(v, 1), (u + v, -1)], some 1, none⟩,
       ⟨form [(u + v, 1), (v, (u : Int) - 1), (W, -1)], some 0, none⟩])).flatten ++
  [⟨form [(W, 1), (u - 1, -(h : Int))], some 0, none⟩]

/-- The state at the start of the search. -/
def St.init (u h : Nat) : St :=
  { u := u, h := h, i := 0, c := fun _ => 0, met := fun _ _ => false,
    rep := fun v => v, off := fun _ => 0, rows := (baseRows u h).reverse }

def St.addRow (st : St) (r : Row) : St := { st with rows := r :: st.rows }

/-- The rows saying that the interval ends before the `i`-th block. -/
def St.addEnd (st : St) : St :=
  { st with rows :=
      ((List.range st.u).map (fun v =>
        (⟨form [(st.tI v, 1), (st.pI v, st.c v), (st.wI, -1)], some 0, none⟩ : Row))).reverse
      ++ st.rows }

/-- The rows placing the point of the `i`-th block. -/
def St.addX (st : St) : St :=
  let r1 : Row :=
    if st.i = 0 then ⟨form [(st.xI 0, 1)], some 0, none⟩
    else ⟨form [(st.xI st.i, 1), (st.xI (st.i - 1), -1)], some 1, none⟩
  let r2 : Row := ⟨form [(st.wI, 1), (st.xI st.i, -1)], some 1, none⟩
  { st with rows := r2 :: r1 :: st.rows }

/-- The form `t v + c v · p v - x i`, the next multiple of `v` relative to the current point. -/
def St.piForm (st : St) (v : Nat) : List Int :=
  form [(st.tI v, 1), (st.xI st.i, -1), (st.pI v, st.c v)]

/-- Every prime has at least `h` blocks. -/
def St.full (st : St) : Bool := (List.range st.u).all (fun v => decide (st.h ≤ st.c v))

/-- Every pair of distinct primes has met. -/
def St.allMet (st : St) : Bool :=
  (List.range st.u).all (fun a => (List.range st.u).all (fun b => a == b || st.met a b))

/-- The primes that `v` has not met yet. -/
def St.unmet (st : St) (v : Nat) : Nat :=
  ((List.range st.u).filter (fun w => w != v && !st.met v w)).length

/-- The prime `v` cannot reach `h` blocks: each later block through it needs a new partner. -/
def St.capOK (st : St) (v : Nat) : Bool := decide (v < st.u) && decide (st.c v + st.unmet v < st.h)

/-- The parity relation for `v` joining a block whose first prime is `s`. -/
def St.parityOK (st : St) (v s : Nat) : Bool :=
  st.rep v != st.rep s || (st.off v + st.off s) % 2 == (st.c v + st.c s) % 2

/-- The rules allow `v` to join the current block, which so far consists of `S`. -/
def St.canJoin (st : St) (v : Nat) (S : List Nat) : Bool :=
  decide (st.c v + 1 < st.u) && S.all (fun s => !st.met v s) &&
    (match S with
     | [] => true
     | s :: _ => st.parityOK v s)

/-- Record the parity relation for `v` joining a block whose first prime is `s`. -/
def St.joinPar (st : St) (v s : Nat) : St :=
  if st.rep v = st.rep s then st
  else
    let rv := st.rep v
    let k := (st.off v + st.off s + st.c v + st.c s) % 2
    { st with
      rep := fun z => if st.rep z = rv then st.rep s else st.rep z,
      off := fun z => if st.rep z = rv then (st.off z + k) % 2 else st.off z }

/-- `v` joins the current block `S`. -/
def St.join (st : St) (v : Nat) (S : List Nat) : St :=
  let st' := match S with
    | [] => st
    | s :: _ => st.joinPar v s
  st'.addRow ⟨st.piForm v, some 0, some 0⟩

/-- `v` stays out of the current block. -/
def St.leave (st : St) (v : Nat) : St := st.addRow ⟨st.piForm v, some 1, none⟩

/-- Close the block `S` and move to the next boundary. -/
def St.next (st : St) (S : List Nat) : St :=
  { st with
    i := st.i + 1,
    c := fun w => if S.contains w then st.c w + 1 else st.c w,
    met := fun a b => st.met a b || (S.contains a && S.contains b) }

/-- Read an unsigned LEB128 number. -/
def readNat (d : ByteArray) (pos : Nat) : Option (Nat × Nat) :=
  go 12 pos 0 0
where
  go : Nat → Nat → Nat → Nat → Option (Nat × Nat)
    | 0, _, _, _ => none
    | fuel + 1, p, acc, sh =>
      if h : p < d.size then
        let b := (d.get p h).toNat
        let acc := acc + (b % 128) * 2 ^ sh
        if b < 128 then some (acc, p + 1) else go fuel (p + 1) acc (sh + 7)
      else none

/-- Read a long unsigned LEB128 number (for certificate multipliers). -/
def readBig (d : ByteArray) (pos : Nat) : Option (Nat × Nat) :=
  go 1024 pos 0 0
where
  go : Nat → Nat → Nat → Nat → Option (Nat × Nat)
    | 0, _, _, _ => none
    | fuel + 1, p, acc, sh =>
      if h : p < d.size then
        let b := (d.get p h).toNat
        let acc := acc + (b % 128) * 2 ^ sh
        if b < 128 then some (acc, p + 1) else go fuel (p + 1) acc (sh + 7)
      else none

def unzigzag (n : Nat) : Int := if n % 2 = 0 then (n / 2 : Nat) else -((n / 2 : Nat) : Int) - 1

/-- Read the entries of a certificate. -/
def readCert (d : ByteArray) : Nat → Nat → Option (List (Nat × Int) × Nat)
  | 0, pos => some ([], pos)
  | m + 1, pos =>
    match readNat d pos with
    | none => none
    | some (k, p1) =>
      match readBig d p1 with
      | none => none
      | some (y, p2) =>
        match readCert d m p2 with
        | none => none
        | some (rest, p3) => some ((k, unzigzag y) :: rest, p3)

/-- Read a certificate (after its tag) and check it against the current rows. -/
def chkCert (st : St) (d : ByteArray) (pos : Nat) : Option Nat :=
  match readNat d pos with
  | none => none
  | some (m, p1) =>
    match readCert d m p1 with
    | none => none
    | some (cert, p2) => if certOK st.rows cert then some p2 else none

/-- Where the checker is in the search tree. -/
inductive Mode where
  | bnd                             -- at a block boundary
  | term                            -- after the rows saying that the interval ends here
  | elem (v : Nat) (S : List Nat)   -- inside a block: `v` is next, `S` has joined so far

/-- Check the subtree of the log that starts at `pos`; return the position after it. -/
def chk : Nat → Mode → St → ByteArray → Nat → Option Nat
  | 0, _, _, _, _ => none
  | fuel + 1, .bnd, st, d, pos =>
    match readNat d pos with
    | none => none
    | some (tag, p1) =>
      if tag = 0 then chkCert st d p1
      else if tag = 1 then
        match readNat d p1 with
        | none => none
        | some (v, p2) => if st.capOK v then some p2 else none
      else if tag = 2 then
        let r1 := if st.full then chk fuel .term st.addEnd d p1 else some p1
        match r1 with
        | none => none
        | some p2 => if st.allMet then some p2 else chk fuel (.elem 0 []) st.addX d p2
      else none
  | _ + 1, .term, st, d, pos =>
    match readNat d pos with
    | none => none
    | some (tag, p1) => if tag = 0 then chkCert st d p1 else none
  | fuel + 1, .elem v S, st, d, pos =>
    if v = st.u then
      (if S.length < 2 then some pos else chk fuel .bnd (st.next S) d pos)
    else
      match readNat d pos with
      | none => none
      | some (tag, p1) =>
        if tag = 0 then chkCert st d p1
        else if tag = 3 then
          let r1 := if st.canJoin v S then chk fuel (.elem (v + 1) (S ++ [v])) (st.join v S) d p1
                    else some p1
          match r1 with
          | none => none
          | some p2 => chk fuel (.elem (v + 1) S) (st.leave v) d p2
        else none

/-- The whole log checks, and nothing is left over. -/
def checkLog (u h : Nat) (d : ByteArray) : Bool :=
  chk 100000 .bnd (St.init u h) d 0 == some d.size

end SweepCheck
