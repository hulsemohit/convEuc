theory doublereverse
	imports Geometry congruencesymmetric congruencetransitive
begin

theorem(in euclidean_geometry) doublereverse:
	assumes 
		"seg_eq A B C D"
	shows "seg_eq D C B A \<and> seg_eq B A D C"
proof -
	have "seg_eq C D D C" using equalityreverseE.
	have "seg_eq A B D C" using congruencetransitive[OF `seg_eq A B C D` `seg_eq C D D C`] .
	have "seg_eq B A A B" using equalityreverseE.
	have "seg_eq B A D C" using congruencetransitive[OF `seg_eq B A A B` `seg_eq A B D C`] .
	have "seg_eq D C B A" using congruencesymmetric[OF `seg_eq B A D C`] .
	have "seg_eq D C B A \<and> seg_eq B A D C" using `seg_eq D C B A` `seg_eq B A D C` by blast
	thus ?thesis by blast
qed

end