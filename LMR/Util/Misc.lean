import Lean

open Lean

namespace List

  variable {α : Type}

  /-- 二つのリストの重複をなくす -/
  protected def union' [DecidableEq α] [Hashable α]
      (l₁ l₂ : List α) : List α := Id.run do
    let mut s := Std.HashSet.empty
    for x in l₁ do
      s := s.insert x
    for x in l₂ do
      s := s.insert x
    return s.toList

  #eval List.union' [1, 2, 3] [2, 4, 3, 1, 1]
  #eval List.union' ["h", "s"] ["a", "s", "b", "h"]

  #eval [1, 2, 3].map Hashable.hash
  #eval ["a", "s", "b", "h"].map Hashable.hash

  def Union [DecidableEq α] [Hashable α] : List (List α) → List α
    | [] => []
    | (l ::ls) => l.union' (ls.Union)

end List
