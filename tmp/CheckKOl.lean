import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.Unique

#print axioms KOl.theta_filtration_drop_classification
#print axioms KOl.theta_half_cycle_filtration
#print axioms KOl.proposition_three_modular
#print axioms KOl.theorem_three
#print axioms KOl.kiming_olsson_theorem_one
#print axioms KOl.ramanujanCongruence_unique

example : partition 0 = 1 := partition_zero
example : partition (-1) = 0 := partition_of_neg (by decide)
