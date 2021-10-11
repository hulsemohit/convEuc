theory lessthanbetween
	imports Geometry betweennotequal layoffunique ray4 ray5
begin

theorem(in euclidean_geometry) lessthanbetween:
	assumes 
		"seg_lt A B A C"
		"ray_on A B C"
	shows "bet A B C"
proof -
	obtain M where "bet A M C \<and> seg_eq A M A B" using lessthan_f[OF `seg_lt A B A C`]  by  blast
	have "bet A M C" using `bet A M C \<and> seg_eq A M A B` by blast
	have "seg_eq A M A B" using `bet A M C \<and> seg_eq A M A B` by blast
	have "A \<noteq> M" using betweennotequal[OF `bet A M C`] by blast
	have "ray_on A M C" using ray4 `bet A M C \<and> seg_eq A M A B` `A \<noteq> M` by blast
	have "ray_on A C M" using ray5[OF `ray_on A M C`] .
	have "ray_on A C B" using ray5[OF `ray_on A B C`] .
	have "M = B" using layoffunique[OF `ray_on A C M` `ray_on A C B` `seg_eq A M A B`] .
	have "bet A B C" using `bet A M C` `M = B` by blast
	thus ?thesis by blast
qed

end