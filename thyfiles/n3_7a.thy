theory n3_7a
	imports n3_6a Geometry betweennotequal congruencesymmetric extensionunique
begin

theorem(in euclidean_geometry) n3_7a:
	assumes 
		"bet A B C"
		"bet B C D"
	shows "bet A C D"
proof -
	have "A \<noteq> C" using betweennotequal[OF `bet A B C`] by blast
	have "C \<noteq> D" using betweennotequal[OF `bet B C D`] by blast
	obtain E where "bet A C E \<and> seg_eq C E C D" using extensionE[OF `A \<noteq> C` `C \<noteq> D`]  by  blast
	have "bet A C E" using `bet A C E \<and> seg_eq C E C D` by blast
	have "seg_eq C E C D" using `bet A C E \<and> seg_eq C E C D` by blast
	have "seg_eq C D C E" using congruencesymmetric[OF `seg_eq C E C D`] .
	have "bet B C E" using n3_6a[OF `bet A B C` `bet A C E`] .
	have "D = E" using extensionunique[OF `bet B C D` `bet B C E` `seg_eq C D C E`] .
	have "bet A C D" using `bet A C E` `D = E` by blast
	thus ?thesis by blast
qed

end