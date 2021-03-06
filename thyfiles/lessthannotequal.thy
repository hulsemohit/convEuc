theory lessthannotequal
	imports Geometry betweennotequal nullsegment3
begin

theorem(in euclidean_geometry) lessthannotequal:
	assumes 
		"seg_lt A B C D"
	shows "A \<noteq> B \<and> C \<noteq> D"
proof -
	obtain E where "bet C E D \<and> seg_eq C E A B" using lessthan_f[OF `seg_lt A B C D`]  by  blast
	have "bet C E D" using `bet C E D \<and> seg_eq C E A B` by blast
	have "seg_eq C E A B" using `bet C E D \<and> seg_eq C E A B` by blast
	have "C \<noteq> E" using betweennotequal[OF `bet C E D`] by blast
	have "A \<noteq> B" using nullsegment3[OF `C \<noteq> E` `seg_eq C E A B`] .
	have "C \<noteq> D" using betweennotequal[OF `bet C E D`] by blast
	have "A \<noteq> B \<and> C \<noteq> D" using `A \<noteq> B` `C \<noteq> D` by blast
	thus ?thesis by blast
qed

end