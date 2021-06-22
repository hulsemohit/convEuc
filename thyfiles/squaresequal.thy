theory squaresequal
	imports Axioms Definitions Theorems
begin

theorem squaresequal:
	assumes: `axioms`
		"seg_eq A B a b"
		"square A B C D"
		"square a b c d"
	shows: "qua_eq_area A B C D a b c d"
proof -
	have "ang_right D A B" using square_f[OF `axioms` `square A B C D`] by blast
	have "ang_right d a b" using square_f[OF `axioms` `square a b c d`] by blast
	have "ang_eq D A B d a b" using Euclid4[OF `axioms` `ang_right D A B` `ang_right d a b`] .
	have "seg_eq A B D A" using square_f[OF `axioms` `square A B C D`] by blast
	have "seg_eq a b d a" using square_f[OF `axioms` `square a b c d`] by blast
	have "seg_eq D A A B" using congruencesymmetric[OF `axioms` `seg_eq A B D A`] .
	have "seg_eq D A a b" using congruencetransitive[OF `axioms` `seg_eq D A A B` `seg_eq A B a b`] .
	have "seg_eq D A d a" using congruencetransitive[OF `axioms` `seg_eq D A a b` `seg_eq a b d a`] .
	have "parallelogram A B C D" using squareparallelogram[OF `axioms` `square A B C D`] .
	have "parallelogram a b c d" using squareparallelogram[OF `axioms` `square a b c d`] .
	have "parallel A B C D" using parallelogram_f[OF `axioms` `parallelogram A B C D`] by blast
	have "parallel a b c d" using parallelogram_f[OF `axioms` `parallelogram a b c d`] by blast
	have "\<not> col A B D" using parallelNC[OF `axioms` `parallel A B C D`] by blast
	have "\<not> col a b d" using parallelNC[OF `axioms` `parallel a b c d`] by blast
	have "seg_eq A D a d" using congruenceflip[OF `axioms` `seg_eq D A d a`] by blast
	have "seg_eq D B d b" using Prop04[OF `axioms` `seg_eq A D a d` `seg_eq A B a b` `ang_eq D A B d a b`] by blast
	have "seg_eq B D b d" using congruenceflip[OF `axioms` `seg_eq D B d b`] by blast
	have "triangle A B D" using triangle_b[OF `axioms` `\<not> col A B D`] .
	have "tri_cong A B D a b d" using trianglecongruence_b[OF `axioms` `seg_eq A B a b` `seg_eq B D b d` `seg_eq A D a d` `triangle A B D`] .
	have "tri_eq_area A B D a b d" using congruentequalE[OF `axioms` `tri_cong A B D a b d`] .
	have "tri_eq_area A B D b d a" using ETpermutationE[OF `axioms` `tri_eq_area A B D a b d`] by blast
	have "tri_eq_area b d a A B D" using ETsymmetricE[OF `axioms` `tri_eq_area A B D b d a`] .
	have "tri_eq_area b d a B D A" using ETpermutationE[OF `axioms` `tri_eq_area b d a A B D`] by blast
	have "tri_eq_area B D A b d a" using ETsymmetricE[OF `axioms` `tri_eq_area b d a B D A`] .
	have "seg_eq A B B C" using square_f[OF `axioms` `square A B C D`] by blast
	have "seg_eq a b b c" using square_f[OF `axioms` `square a b c d`] by blast
	have "seg_eq A B C D" using square_f[OF `axioms` `square A B C D`] by blast
	have "seg_eq a b c d" using square_f[OF `axioms` `square a b c d`] by blast
	have "seg_eq B C A B" using congruencesymmetric[OF `axioms` `seg_eq A B B C`] .
	have "seg_eq B C a b" using congruencetransitive[OF `axioms` `seg_eq B C A B` `seg_eq A B a b`] .
	have "seg_eq B C b c" using congruencetransitive[OF `axioms` `seg_eq B C a b` `seg_eq a b b c`] .
	have "seg_eq C D A B" using congruencesymmetric[OF `axioms` `seg_eq A B C D`] .
	have "seg_eq C D a b" using congruencetransitive[OF `axioms` `seg_eq C D A B` `seg_eq A B a b`] .
	have "seg_eq C D c d" using congruencetransitive[OF `axioms` `seg_eq C D a b` `seg_eq a b c d`] .
	have "\<not> col B C D" using parallelNC[OF `axioms` `parallel A B C D`] by blast
	have "triangle B C D" using triangle_b[OF `axioms` `\<not> col B C D`] .
	have "tri_cong B C D b c d" using trianglecongruence_b[OF `axioms` `seg_eq B C b c` `seg_eq C D c d` `seg_eq B D b d` `triangle B C D`] .
	have "tri_eq_area B C D b c d" using congruentequalE[OF `axioms` `tri_cong B C D b c d`] .
	have "tri_eq_area B C D b d c" using ETpermutationE[OF `axioms` `tri_eq_area B C D b c d`] by blast
	have "tri_eq_area b d c B C D" using ETsymmetricE[OF `axioms` `tri_eq_area B C D b d c`] .
	have "tri_eq_area b d c B D C" using ETpermutationE[OF `axioms` `tri_eq_area b d c B C D`] by blast
	have "tri_eq_area B D C b d c" using ETsymmetricE[OF `axioms` `tri_eq_area b d c B D C`] .
	have "rectangle A B C D" using squarerectangle[OF `axioms` `square A B C D`] .
	have "cross A C B D" using rectangle_f[OF `axioms` `rectangle A B C D`] by blast
	obtain M where "bet A M C \<and> bet B M D" using cross_f[OF `axioms` `cross A C B D`] by blast
	have "bet A M C" using `bet A M C \<and> bet B M D` by blast
	have "bet B M D" using `bet A M C \<and> bet B M D` by blast
	have "rectangle a b c d" using squarerectangle[OF `axioms` `square a b c d`] .
	have "cross a c b d" using rectangle_f[OF `axioms` `rectangle a b c d`] by blast
	obtain m where "bet a m c \<and> bet b m d" using cross_f[OF `axioms` `cross a c b d`] by blast
	have "bet a m c" using `bet a m c \<and> bet b m d` by blast
	have "bet b m d" using `bet a m c \<and> bet b m d` by blast
	have "tri_eq_area B D A b d a" using `tri_eq_area B D A b d a` .
	have "tri_eq_area B D C b d c" using `tri_eq_area B D C b d c` .
	have "qua_eq_area B A D C b a d c" sorry
	have "qua_eq_area B A D C a b c d" using EFpermutationE[OF `axioms` `qua_eq_area B A D C b a d c`] by blast
	have "qua_eq_area a b c d B A D C" using EFsymmetricE[OF `axioms` `qua_eq_area B A D C a b c d`] .
	have "qua_eq_area a b c d A B C D" using EFpermutationE[OF `axioms` `qua_eq_area a b c d B A D C`] by blast
	have "qua_eq_area A B C D a b c d" using EFsymmetricE[OF `axioms` `qua_eq_area a b c d A B C D`] .
	thus ?thesis by blast
qed

end