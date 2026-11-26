import EditCodes.Basic

namespace EditCodes.Ternary

/-- The empty word and seven long words. -/
def witness : List (List (Fin 3)) := [
  [],
  [0,0,0,0,0,0],
  [0,0,1,1,1,1,1,1],
  [0,0,2,2,2,2,2,2],
  [1,1,0,0,1,1,2,2],
  [1,1,1,2,0,2,0,1],
  [2,2,0,0,2,2,1,1],
  [2,2,2,1,0,1,0,2]]

set_option maxHeartbeats 1000000 in
theorem witness_isCode : IsCode 8 6 witness := by
  constructor <;> decide +kernel

theorem lower_bound : ∃ C : List (List (Fin 3)),
    IsCode 8 6 C ∧ C.length = 8 ∧ ∃ w ∈ C, w.length = 8 :=
  ⟨witness, witness_isCode, rfl, [0,0,1,1,1,1,1,1], by decide, rfl⟩

end EditCodes.Ternary
