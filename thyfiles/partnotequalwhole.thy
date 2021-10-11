theory partnotequalwhole
	imports n3_7b Geometry betweennotequal extensionunique inequalitysymmetric
begin

theorem(in euclidean_geometry) partnotequalwhole:
	assumes 
		"bet A B C"
	shows "\<not> (seg_eq A B A C)"
proof -
	have "A \<noteq> B" using betweennotequal[OF `bet A B C`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	obtain D where "bet B A D \<and> seg_eq A D B A" using extensionE[OF `B \<noteq> A` `B \<noteq> A`]  by  blast
	have "bet B A D" using `bet B A D \<and> seg_eq A D B A` by blast
	have "bet D A B" using betweennesssymmetryE[OF `bet B A D`] .
	have "bet D A C" using n3_7b[OF `bet D A B` `bet A B C`] .
	have "bet A B C" using `bet A B C` .
	have "B \<noteq> C" using betweennotequal[OF `bet A B C`] by blast
	have "\<not> (seg_eq A B A C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (seg_eq A B A C))"
hence "seg_eq A B A C" by blast
		have "B = C" using extensionunique[OF `bet D A B` `bet D A C` `seg_eq A B A C`] .
		show "False" using `B = C` `B \<noteq> C` by blast
	qed
	hence "\<not> (seg_eq A B A C)" by blast
	thus ?thesis by blast
qed

end