import EditCodes.Graph
import EditCodes.CliqueSearch

namespace EditCodes.Ternary
open Search

abbrev adjacency (rows : Array Nat) (i : Nat) := rows[i]?.getD 0

def hasEdge (G : Neighbours) (pool : Nat) : Bool :=
  (members pool).any fun v => (pool &&& G v) != 0

/-- If another vertex of the original colour remains, keep the branch. Otherwise
five further vertices use two colours and contain a second monochromatic triple. -/
def possibleFive (G : Neighbours) (c pool : Nat) : Bool :=
  ((pool &&& colourMask c) != 0) ||
    [0,1,2].any fun b => b != c &&
      choose G (hasEdge G) 3 (pool &&& colourMask b) pool

/-- Eight long words would have a monochromatic triple of first letters. After
that triple is chosen, look for the other five in its common neighbourhood. -/
def possibleEight (size : Nat) : Bool :=
  let rows := graphFor size
  let G := adjacency rows
  [0, 1, 2].any fun c => parallelStep G (possibleFive G c) 2 (colourMask c) longMask

end EditCodes.Ternary
