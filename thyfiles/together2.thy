theory together2
	imports n3_6a n3_7a n3_7b Geometry betweennotequal collinear4 collinearorder congruenceflip congruencesymmetric congruencetransitive equalitysymmetric inequalitysymmetric lessthanadditive lessthantransitive nullsegment3 outerconnectivity ray1 ray4 rayimpliescollinear raystrict together trichotomy2 tworays
begin

theorem together2:
	assumes "axioms"
		"seg_sum_gt A a C c B b"
		"seg_eq F G B b"
		"ray_on F G M"
		"seg_eq F M A a"
		"ray_on G F N"
		"seg_eq G N C c"
	shows "ray_on M F N"
proof -
	obtain J where "bet A a J \<and> seg_eq a J C c \<and> seg_lt B b A J" using togethergreater_f[OF `axioms` `seg_sum_gt A a C c B b`]  by  blast
	have "bet A a J" using `bet A a J \<and> seg_eq a J C c \<and> seg_lt B b A J` by blast
	have "seg_eq a J C c" using `bet A a J \<and> seg_eq a J C c \<and> seg_lt B b A J` by blast
	have "a \<noteq> J" using betweennotequal[OF `axioms` `bet A a J`] by blast
	have "C \<noteq> c" using nullsegment3[OF `axioms` `a \<noteq> J` `seg_eq a J C c`] .
	have "\<not> (M = N)"
	proof (rule ccontr)
		assume "\<not> (M \<noteq> N)"
		hence "M = N" by blast
		have "ray_on G F N" using `ray_on G F N` .
		have "ray_on F G N" using `ray_on F G M` `M = N` by blast
		have "ray_on G F M" using `ray_on G F N` `M = N` by blast
		have "bet F M G" using tworays[OF `axioms` `ray_on F G M` `ray_on G F M`] .
		have "seg_eq G M C c" using `seg_eq G N C c` `M = N` by blast
		have "seg_eq M G C c" using congruenceflip[OF `axioms` `seg_eq G M C c`] by blast
		have "seg_lt F G F G" using together[OF `axioms` `seg_sum_gt A a C c B b` `seg_eq F M A a` `seg_eq M G C c` `bet F M G` `seg_eq F G B b`] by blast
		have "\<not> (seg_lt F G F G)" using trichotomy2[OF `axioms` `seg_lt F G F G`] .
		show "False" using `\<not> (seg_lt F G F G)` `seg_lt F G F G` by blast
	qed
	hence "M \<noteq> N" by blast
	have "F \<noteq> M" using raystrict[OF `axioms` `ray_on F G M`] .
	have "M \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> M`] .
	obtain D where "bet M F D \<and> seg_eq F D M F" using extensionE[OF `axioms` `M \<noteq> F` `M \<noteq> F`]  by  blast
	have "bet M F D" using `bet M F D \<and> seg_eq F D M F` by blast
	have "ray_on F G M" using `ray_on F G M` .
	have "bet F M G \<or> G = M \<or> bet F G M" using ray1[OF `axioms` `ray_on F G M`] .
	consider "bet F M G"|"G = M"|"bet F G M" using `bet F M G \<or> G = M \<or> bet F G M`  by blast
	hence "bet G F D"
	proof (cases)
		assume "bet F M G"
		have "bet G M F" using betweennesssymmetryE[OF `axioms` `bet F M G`] .
		have "bet M F D" using `bet M F D` .
		have "bet G F D" using n3_7a[OF `axioms` `bet G M F` `bet M F D`] .
		thus ?thesis by blast
	next
		assume "G = M"
		have "bet M F D" using `bet M F D` .
		have "bet G F D" using `bet M F D` `G = M` by blast
		thus ?thesis by blast
	next
		assume "bet F G M"
		have "bet M G F" using betweennesssymmetryE[OF `axioms` `bet F G M`] .
		have "bet M F D" using `bet M F D` .
		have "bet G F D" using n3_6a[OF `axioms` `bet M G F` `bet M F D`] .
		thus ?thesis by blast
	qed
	have "bet D F M" using betweennesssymmetryE[OF `axioms` `bet M F D`] .
	have "bet D F G" using betweennesssymmetryE[OF `axioms` `bet G F D`] .
	have "\<not> (bet F M N)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet F M N))"
hence "bet F M N" by blast
		have "F \<noteq> M" using betweennotequal[OF `axioms` `bet D F M`] by blast
		have "C \<noteq> c" using `C \<noteq> c` .
		obtain P where "bet F M P \<and> seg_eq M P C c" using extensionE[OF `axioms` `F \<noteq> M` `C \<noteq> c`]  by  blast
		have "bet F M P" using `bet F M P \<and> seg_eq M P C c` by blast
		have "seg_eq F M A a" using `seg_eq F M A a` .
		have "seg_eq M P C c" using `bet F M P \<and> seg_eq M P C c` by blast
		have "seg_eq F G B b" using `seg_eq F G B b` .
		have "seg_lt F G F P" using together[OF `axioms` `seg_sum_gt A a C c B b` `seg_eq F M A a` `seg_eq M P C c` `bet F M P` `seg_eq F G B b`] by blast
		have "seg_eq C c G N" using congruencesymmetric[OF `axioms` `seg_eq G N C c`] .
		have "seg_eq C c N G" using congruenceflip[OF `axioms` `seg_eq C c G N`] by blast
		have "seg_eq M P N G" using congruencetransitive[OF `axioms` `seg_eq M P C c` `seg_eq C c N G`] .
		have "seg_eq F M F M" using congruencereflexiveE[OF `axioms`] .
		have "seg_lt F M F N" using lessthan_b[OF `axioms` `bet F M N` `seg_eq F M F M`] .
		have "bet F M P" using `bet F M P` .
		have "seg_eq M P N G" using `seg_eq M P N G` .
		have "\<not> (bet F N G)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet F N G))"
hence "bet F N G" by blast
			have "seg_lt F P F G" using lessthanadditive[OF `axioms` `seg_lt F M F N` `bet F M P` `bet F N G` `seg_eq M P N G`] .
			have "seg_lt F G F P" using `seg_lt F G F P` .
			have "seg_lt F G F G" using lessthantransitive[OF `axioms` `seg_lt F G F P` `seg_lt F P F G`] .
			have "\<not> (seg_lt F G F G)" using trichotomy2[OF `axioms` `seg_lt F G F G`] .
			show "False" using `\<not> (seg_lt F G F G)` `seg_lt F G F G` by blast
		qed
		hence "\<not> (bet F N G)" by blast
		have "\<not> (bet G N F)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet G N F))"
hence "bet G N F" by blast
			have "bet F N G" using betweennesssymmetryE[OF `axioms` `bet G N F`] .
			show "False" using `bet F N G` `\<not> (bet F N G)` by blast
		qed
		hence "\<not> (bet G N F)" by blast
		have "bet F M N" using `bet F M N` .
		have "ray_on G F N" using `ray_on G F N` .
		have "bet G N F \<or> F = N \<or> bet G F N" using ray1[OF `axioms` `ray_on G F N`] .
		have "F = N \<or> bet G F N" using `bet G N F \<or> F = N \<or> bet G F N` `\<not> (bet G N F)` by blast
		have "F \<noteq> N" using betweennotequal[OF `axioms` `bet F M N`] by blast
		have "\<not> (\<not> (bet G F N))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet G F N)))"
hence "\<not> (bet G F N)" by blast
			have "F \<noteq> N \<and> \<not> (bet G F N)" using `F \<noteq> N` `\<not> (bet G F N)` by blast
			show "False" using `F \<noteq> N \<and> \<not> (bet G F N)` `F = N \<or> bet G F N` by blast
		qed
		hence "bet G F N" by blast
		have "bet N F G" using betweennesssymmetryE[OF `axioms` `bet G F N`] .
		have "bet D F M" using `bet D F M` .
		have "bet D F G" using `bet D F G` .
		have "\<not> (\<not> (bet N F M))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet N F M)))"
hence "\<not> (bet N F M)" by blast
			have "\<not> (bet F M G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (bet F M G))"
hence "bet F M G" by blast
				have "bet N F G" using `bet N F G` .
				have "bet N F M" using innertransitivityE[OF `axioms` `bet N F G` `bet F M G`] .
				show "False" using `bet N F M` `\<not> (bet N F M)` by blast
			qed
			hence "\<not> (bet F M G)" by blast
			have "\<not> (bet F G M)"
			proof (rule ccontr)
				assume "\<not> (\<not> (bet F G M))"
hence "bet F G M" by blast
				have "bet N F G" using `bet N F G` .
				have "bet N F M" using n3_7b[OF `axioms` `bet N F G` `bet F G M`] .
				show "False" using `bet N F M` `\<not> (bet N F M)` by blast
			qed
			hence "\<not> (bet F G M)" by blast
			have "G = M" using outerconnectivity[OF `axioms` `bet D F G` `bet D F M` `\<not> (bet F G M)` `\<not> (bet F M G)`] .
			have "bet N F M" using `bet N F G` `G = M` by blast
			show "False" using `bet N F M` `\<not> (bet N F M)` by blast
		qed
		hence "bet N F M" by blast
		have "bet F M N" using `bet F M N` .
		have "bet N F N" using n3_7b[OF `axioms` `bet N F M` `bet F M N`] .
		have "\<not> (bet N F N)" using betweennessidentityE[OF `axioms`] .
		show "False" using `\<not> (bet N F N)` `bet N F N` by blast
	qed
	hence "\<not> (bet F M N)" by blast
	have "col G F N" using rayimpliescollinear[OF `axioms` `ray_on G F N`] .
	have "col F G M" using rayimpliescollinear[OF `axioms` `ray_on F G M`] .
	have "col G F M" using collinearorder[OF `axioms` `col F G M`] by blast
	have "F \<noteq> G" using betweennotequal[OF `axioms` `bet D F G`] by blast
	have "G \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> G`] .
	have "col F N M" using collinear4[OF `axioms` `col G F N` `col G F M` `G \<noteq> F`] .
	have "col M F N" using collinearorder[OF `axioms` `col F N M`] by blast
	have "M = F \<or> M = N \<or> F = N \<or> bet F M N \<or> bet M F N \<or> bet M N F" using collinear_f[OF `axioms` `col M F N`] .
	consider "M = F"|"M = N"|"F = N"|"bet F M N"|"bet M F N"|"bet M N F" using `M = F \<or> M = N \<or> F = N \<or> bet F M N \<or> bet M F N \<or> bet M N F`  by blast
	hence "ray_on M F N"
	proof (cases)
		assume "M = F"
		have "\<not> (\<not> (ray_on M F N))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on M F N)))"
hence "\<not> (ray_on M F N)" by blast
			have "M \<noteq> F" using `M \<noteq> F` .
			show "False" using `M \<noteq> F` `M = F` by blast
		qed
		hence "ray_on M F N" by blast
		thus ?thesis by blast
	next
		assume "M = N"
		have "\<not> (\<not> (ray_on M F N))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on M F N)))"
hence "\<not> (ray_on M F N)" by blast
			have "M \<noteq> N" using `M \<noteq> N` .
			show "False" using `M \<noteq> N` `M = N` by blast
		qed
		hence "ray_on M F N" by blast
		thus ?thesis by blast
	next
		assume "F = N"
		have "N = F" using equalitysymmetric[OF `axioms` `F = N`] .
		have "ray_on M F N" using ray4 `axioms` `N = F` `M \<noteq> F` by blast
		thus ?thesis by blast
	next
		assume "bet F M N"
		have "\<not> (\<not> (ray_on M F N))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on M F N)))"
hence "\<not> (ray_on M F N)" by blast
			have "\<not> (bet F M N)" using `\<not> (bet F M N)` .
			show "False" using `\<not> (bet F M N)` `bet F M N` by blast
		qed
		hence "ray_on M F N" by blast
		thus ?thesis by blast
	next
		assume "bet M F N"
		have "ray_on M F N" using ray4 `axioms` `bet M F N` `M \<noteq> F` by blast
		thus ?thesis by blast
	next
		assume "bet M N F"
		have "ray_on M F N" using ray4 `axioms` `bet M N F` `M \<noteq> F` by blast
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end