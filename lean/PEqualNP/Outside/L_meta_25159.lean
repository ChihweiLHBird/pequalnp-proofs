import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_25159

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [9]⟩,
    ⟨.or, [8, 10]⟩], 11⟩

end PEqualNP.Outside.L_meta_25159

open PEqualNP.Outside.L_meta_25159 in
theorem PEqualNP.Outside.L_meta_25159 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16824 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, by simp [PEqualNP.MetaComplexity.FanInTwo, witness], by decide, by decide +kernel⟩
