namespace WBT.Node

structure Node (α: Type u) where
  weight: Nat
  height: Nat
  entry: α
  left?: Option (Node α)
  right?: Option (Node α)

partial def iterate (n?: Option (Node α)): Array α :=
  match n? with
    | none => #[]
    | some n =>
      let (l, r) := (iterate n.left?, iterate n.right?)
      l ++ #[n.entry] ++ r

def weight (n?: Option (Node α)): Nat :=
  match n? with
    | none => 0
    | some n => n.weight

def height (n?: Option (Node α)): Nat :=
  match n? with
    | none => 0
    | some n => n.height

partial def left (n?: Option (Node α)): Option α :=
  match n? with
    | none => none
    | some n =>
      match n.left? with
        | none => n.entry
        | some l => left l

instance: Repr (Node α) where
  reprPrec (n: Node α) (_: Nat): Std.Format :=
    s!"Node(w={n.weight}, h={n.height}, lw={weight n.left?}, rw={weight n.right?}, lh={height n.left?}, rh={height n.right?})"

def makeNode (entry: α) (left?: Option (Node α)) (right?: Option (Node α)): Node α :=
  {
    weight := 1 + weight left? + weight right?,
    height := 1 + max (height left?) (height right?),
    entry := entry,
    left? := left?,
    right? := right?,
  }

instance [Inhabited α]: Inhabited (Node α) where
  default := makeNode default none none

partial def cmp (δ: Nat) (n: Option (Node α)): Ordering :=
  match n with
    | none => Ordering.eq
    | some n =>
      let (l, r) := (weight n.left?, weight n.right?)
      if l + r ≤ 1 then
        Ordering.eq
      else if (l > δ * r) then
        Ordering.gt -- left heavy
      else if (δ * l < r) then
        Ordering.lt -- right heavy
      else
        Ordering.eq

partial def cmpWeak (δ: Nat) (n: Option (Node α)): Ordering :=
  match n with
    | none => Ordering.eq
    | some n =>
      let (l, r) := (weight n.left?, weight n.right?)
      if l + r ≤ 2 then
        Ordering.eq
      else if (l > δ * r + 1) then
        Ordering.gt -- left heavy
      else if (δ * l + 1 < r) then
        Ordering.lt -- right heavy
      else
        Ordering.eq

partial def balanceCond (δ: Nat) (n: Option (Node α)): Bool :=
    match n with
    | none => true
    | some n =>
      (balanceCond δ n.left?)
        ∧
      (balanceCond δ n.right?)
        ∧
      (Ordering.eq = cmp δ (some n))

partial def weakBalanceCond (δ: Nat) (n: Option (Node α)): Bool :=
    match n with
    | none => true
    | some n =>
      (weakBalanceCond δ n.left?)
        ∧
      (weakBalanceCond δ n.right?)
        ∧
      (Ordering.eq = cmpWeak δ (some n))

def rightRotate (n: Node α) (hl: n.left?.isSome): Node α :=
  -- right rotate
  --         n
  --   l           r
  -- ll lr
  --
  --      becomes
  --
  --         l
  --   ll          n
  --             lr r
  let l := n.left?.get hl
  let r? := n.right?
  let (ll?, lr?) := (l.left?, l.right?)

  let n1 := makeNode n.entry lr? r?
  let l1 := makeNode l.entry ll? n1
  l1

def leftRotate (n: Node α) (hr: n.right?.isSome): Node α :=
  -- left rotate
  --         n
  --   l           r
  --             rl rr
  --
  --      becomes
  --
  --         r
  --   n          rr
  --  l rl
  let r := n.right?.get hr
  let l? := n.left?
  let (rl?, rr?) := (r.left?, r.right?)

  let n1 := makeNode n.entry l? rl?
  let r1 := makeNode r.entry n1 rr?
  r1

partial def wbtBalance (δ: Nat) (n: Node α): Node α :=
  -- assuming δ ≥ 3
  -- assuming the two subtrees n.left and n.right are balanced
  -- do single rotation or double rotation to rebalance the tree
  -- double rotation is necessary - see `why_double_rotation.jpeg`
  -- will be be sufficient for merge and split? TODO
  let n1 :=
    match cmp δ (some n) with
      | Ordering.eq => n
      | Ordering.gt => -- left heavy
        let n1 := rightRotate n sorry
        if cmp δ (some n1) = Ordering.eq then
          n1
        else
          -- not balanced after one single rotation
          -- because lr too heavy
          -- double rotation effectively split lr in half
          let l := n.left?.get sorry
          let l1 := leftRotate l sorry
          let n2 := makeNode n.entry l1 n.right?
          let n3 := rightRotate n2 sorry
          n3
      | Ordering.lt => -- right heavy
        let n1 := leftRotate n sorry
        if cmp δ (some n1) = Ordering.eq then
          n1
        else
          -- not balanced after one single rotation
          -- because rl too heavy
          -- double rotation effectively split rl in half
          let r := n.right?.get sorry
          let r1 := rightRotate r sorry
          let n2 := makeNode n.entry n.left? r1
          let n3 := leftRotate n2 sorry
          n3

  -- dbg
  if ¬ (balanceCond δ (some n1)) then
    dbg_trace s!"[DBG_TRACE] output_not_eq {repr n1}"
    if ¬ (weakBalanceCond δ (some n)) then
      dbg_trace s!"[DBG_TRACE] input_not_weak_eq {repr n}"
      n1
    else
      n1
  else
    n1

def wbtBalanceThmWeak (δ: Nat) (n: Node α):
  δ ≥ 3
  → balanceCond δ n.left?
  → balanceCond δ n.right?
  → Ordering.eq = cmpWeak δ (some n)
  → balanceCond δ (some (wbtBalance δ n))
  := sorry

def wbtBalanceThm (δ: Nat) (n: Node α):
  δ ≥ 3
  → balanceCond δ n.left?
  → balanceCond δ n.right?
  → balanceCond δ (some (wbtBalance δ n))
  := sorry

def δ := 3

end WBT.Node
