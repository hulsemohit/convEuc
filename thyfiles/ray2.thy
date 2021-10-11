theory ray2
	imports Geometry betweennotequal
begin

theorem(in euclidean_geometry) ray2:
	assumes 
		"ray_on A B C"
	shows "A \<noteq> B"
proof -
	obtain E where "bet E A C \<and> bet E A B" using ray_f[OF `ray_on A B C`]  by  blast
	have "bet E A B" using `bet E A C \<and> bet E A B` by blast
	have "A \<noteq> B" using betweennotequal[OF `bet E A B`] by blast
	thus ?thesis by blast
qed

end