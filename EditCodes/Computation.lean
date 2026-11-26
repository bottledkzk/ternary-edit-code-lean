import EditCodes.Decision

namespace EditCodes.Ternary

/-- The single native computation in the upper bound. -/
theorem search_empty : possibleEight universeSize = false := by native_decide

end EditCodes.Ternary
