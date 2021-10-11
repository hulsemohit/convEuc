theory layoff
	imports Geometry betweennotequal equalitysymmetric
begin

theorem(in euclidean_geometry) layoff:
	assumes 
		"A \<noteq> B"
		"C \<noteq> D"
	shows "\<exists> P. ray_on A B P \<and> seg_eq A P C D"
proof -
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> A)"
		hence "B = A" by blast
		have "A = B" using equalitysymmetric[OF `B = A`] .
		show "False" using `A = B` `A \<noteq> B` by blast
	qed
	hence "B \<noteq> A" by blast
	obtain E where "bet B A E \<and> seg_eq A E C D" using extensionE[OF `B \<noteq> A` `C \<noteq> D`]  by  blast
	have "bet B A E" using `bet B A E \<and> seg_eq A E C D` by blast
	have "bet E A B" using betweennesssymmetryE[OF `bet B A E`] .
	have "E \<noteq> A" using betweennotequal[OF `bet E A B`] by blast
	have "bet E A B" using betweennesssymmetryE[OF `bet B A E`] .
	obtain P where "bet E A P \<and> seg_eq A P C D" using extensionE[OF `E \<noteq> A` `C \<noteq> D`]  by  blast
	have "bet E A P" using `bet E A P \<and> seg_eq A P C D` by blast
	have "seg_eq A P C D" using `bet E A P \<and> seg_eq A P C D` by blast
	have "ray_on A B P" using ray_b[OF `bet E A P` `bet E A B`] .
	have "ray_on A B P \<and> seg_eq A P C D" using `ray_on A B P` `bet E A P \<and> seg_eq A P C D` by blast
	thus ?thesis by blast
qed

end