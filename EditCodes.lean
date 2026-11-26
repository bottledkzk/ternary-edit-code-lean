import EditCodes.Alignment
import EditCodes.Computation
import EditCodes.Reduction
import EditCodes.Witness

namespace EditCodes.Ternary

/-- The exact size of a variable-length ternary edit code for (n,d) = (8,6). -/
theorem optimal_8_6 : OptimalSize (Fin 3) 8 6 8 :=
  ⟨lower_bound, upper_of_search search_empty⟩

end EditCodes.Ternary

#print axioms EditCodes.Ternary.witness_isCode
#print axioms EditCodes.Ternary.optimal_8_6
