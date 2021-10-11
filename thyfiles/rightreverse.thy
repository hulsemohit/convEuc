theory rightreverse
	imports Geometry congruenceflip congruencesymmetric congruencetransitive extensionunique
begin

theorem(in euclidean_geometry) rightreverse:
	assumes 
		"ang_right A B C"
		"bet A B D"
		"seg_eq A B B D"
	shows "seg_eq A C D C"
proof -
	obtain E where "bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C" using rightangle_f[OF `ang_right A B C`]  by  blast
	have "bet A B E" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` by blast
	have "seg_eq A B E B" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` by blast
	have "seg_eq A C E C" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` by blast
	have "seg_eq B D A B" using congruencesymmetric[OF `seg_eq A B B D`] .
	have "seg_eq B D E B" using congruencetransitive[OF `seg_eq B D A B` `seg_eq A B E B`] .
	have "seg_eq B D B E" using congruenceflip[OF `seg_eq B D E B`] by blast
	have "D = E" using extensionunique[OF `bet A B D` `bet A B E` `seg_eq B D B E`] .
	have "seg_eq A C D C" using `seg_eq A C E C` `D = E` by blast
	thus ?thesis by blast
qed

end