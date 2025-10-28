import WBT.WBT

open WBT

def lift (o: Option α): IO α :=
  match o with
    | none => throw $ IO.Error.userError "Cannot lift 'none' into 'IO'"
    | some v => pure v

def example_arr : IO Unit := do
  -- long array
  let a := WBTArr.fromArray (Array.replicate 1000 0)
  IO.println s!"long_array: a.length = {a.length} a.depth = {a.depth}"
  let a := WBTArr.fromArray (Array.replicate 2000 0)
  IO.println s!"long_array: a.length = {a.length} a.depth = {a.depth}"
  let a := WBTArr.fromArray (Array.replicate 3000 0)
  IO.println s!"long_array: a.length = {a.length} a.depth = {a.depth}"
  let a := WBTArr.fromArray (Array.replicate 4000 0)
  IO.println s!"long_array: a.length = {a.length} a.depth = {a.depth}"

  -- array manipulation
  let a: WBTArr Nat := WBTArr.empty
    |> (·.push 1) |> (·.push 2) |> (·.push 3)
  IO.println s!"array_manipulation {a.toArray}"
  let x ← lift $ a.get? 2
  IO.println s!"array_manipulation_get_2 {x}"
  let a ← lift $ a.insert? 0 0
  IO.println s!"array_manipulation_prepend {a.toArray}"
  let a := a.push 4
  IO.println s!"array_manipulation_append {a.toArray}"
  let a ← lift $ a.insert? 2 20
  IO.println s!"array_manipulation_insert {a.toArray}"
  let a ← lift $ a.delete? 3
  IO.println s!"array_manipulation_delete {a.toArray}"

  -- array manipulation bulk
  -- TODO merge and split

def example_map : IO Unit := do
  -- map manipulation
  let m: WBTMap Nat String compare := WBTMap.empty
    |> (·.set 1 "1") |> (·.set 2 "2") |> (·.set 3 "3")
  IO.println s!"map_manipulation {repr m.toArray}"
  let x ← lift $ m.get? 3
  IO.println s!"map_manipulation_get_3 {repr x}"
  let m := m.set 2 "two"
  IO.println s!"map_manipulation_set {repr m.toArray}"
  let m := m.del 3
  IO.println s!"map_manipulation_del {repr m.toArray}"


  -- map manipulation bulk
  -- TODO merge and split

def main : IO Unit := do
  example_arr
  example_map
